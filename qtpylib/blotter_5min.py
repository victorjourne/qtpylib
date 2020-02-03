#!/usr/bin/env python
# -*- coding: utf-8 -*-
#
# QTPyLib: Quantitative Trading Python Library
# https://github.com/ranaroussi/qtpylib
#
# Copyright 2016-2018 Ran Aroussi
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

import argparse
import atexit
import json
import logging
import os
import pickle

import sys
import tempfile
import time
import glob
import subprocess

from datetime import datetime, timedelta
from abc import ABCMeta

import zmq
import pandas as pd
from dateutil.parser import parse as parse_date

import pymysql
from pymysql.constants.CLIENT import MULTI_STATEMENTS

from numpy import (
    isnan as np_isnan,
    nan as np_nan,
    int64 as np_int64
)

from ezibpy import (
    ezIBpy, dataTypes as ibDataTypes
)

from qtpylib import (
    tools, asynctools, path, futures, __version__
)


# =============================================
# check min, python version
if sys.version_info < (3, 4):
    raise SystemError("QTPyLib requires Python version >= 3.4")

# =============================================
# Configure logging
tools.createLogger(__name__, logging.INFO)

# Disable ezIBpy logging (Blotter handles errors itself)
logging.getLogger('ezibpy').setLevel(logging.CRITICAL)

# =============================================
# set up threading pool
__threads__ = tools.read_single_argv("--threads")
__threads__ = __threads__ if tools.is_number(__threads__) else None
asynctools.multitasking.createPool(__name__, __threads__)

# =============================================

cash_ticks = {}

def timing(f):
    def wrap(*args):
        time1 = time.time()
        ret = f(*args)

        time2 = time.time()
        if 1000.*(time2 - time1) > 100: # ms
            if args[2] == 'BAR':
                if "missing" in args[1] :
                    print('{:s} function took {:.3f} ms to execute {} {:s} ({}-{}-missing)'.format(f.__name__, (time2-time1)*1000.0,args[1]['granularity'], args[2], args[1]['timestamp'], args[1]['symbol']))
                else:
                    print('{:s} function took {:.3f} ms to execute {} {:s} ({}-{})'.format(f.__name__, (time2-time1)*1000.0,args[1]['granularity'], args[2], args[1]['timestamp'], args[1]['symbol']))

            else:
                print('{:s} function took {:.3f} ms to execute {:s}'.format(f.__name__, (time2-time1)*1000.0, args[2]))

        return ret
    return wrap

class Blotter():
    """Broker class initilizer

    :Optional:

        name : string
            name of the blotter (used by other modules)
        symbols : str
            IB contracts CSV database (default: ./symbols.csv)
        ibport : int
            TWS/GW Port to use (default: 4001)
        ibclient : int
            TWS/GW Client ID (default: 999)
        ibserver : str
            IB TWS/GW Server hostname (default: localhost)
        zmqport : str
            ZeroMQ Port to use (default: 12345)
        zmqtopic : str
            ZeroMQ string to use (default: _qtpylib_BLOTTERNAME_)
        orderbook : str
            Get Order Book (Market Depth) data (default: False)
        dbhost : str
            MySQL server hostname (default: localhost)
        dbport : str
            MySQL server port (default: 3306)
        dbname : str
            MySQL server database (default: qpy)
        dbuser : str
            MySQL server username (default: root)
        dbpass : str
            MySQL server password (default: none)
        dbskip : str
            Skip MySQL logging (default: False)
    """

    __metaclass__ = ABCMeta

    def __init__(self, name=None, symbols="symbols.csv",
                 ibport=4001, ibclient=999, ibserver="localhost",
                 dbhost="localhost", dbport="3306", dbname="qtpy",
                 dbuser="root", dbpass="", dbskip=False, orderbook=False,
                 zmqport="12345", zmqtopic=None,barsize=1, **kwargs):

        # whats my name?
        #self.name = str(self.__class__).split('.')[-1].split("'")[0].lower()
        self.name = tools.read_single_argv("--name")
        if name is not None:
            self.name = name
        print("name is : %s"%self.name )
        # initilize class logge 2>&1r
        self.log_blotter = logging.getLogger(__name__)

        # -------------------------------
        # work default values
        # -------------------------------
        self.market = tools.read_single_argv("--market")
        if zmqtopic is None:
            zmqtopic = "_qtpylib_" + str(self.market.lower()) + "_"
        print("zmqtopic is : %s"%zmqtopic)
        # if no path given for symbols' csv, use same dir
        if symbols == "symbols.csv":
            symbols = path['caller'] + '/' + symbols
        # do not act on first tick (timezone is incorrect)
        self.first_tick = True
        now = datetime.now()
        self._bars = pd.DataFrame(
            columns=['open', 'high', 'low', 'close', 'volume'])
        self._bars.index.names = ['datetime']
        self._bars.index = pd.to_datetime(self._bars.index, utc=True)
        # self._bars.index = self._bars.index.tz_convert(settings['timezone'])
        self._bars = {"~": self._bars}

        self._raw_bars = pd.DataFrame(columns=['last', 'volume', 'symbol_group', 'asset_class'])
        self._raw_bars.index.names = ['datetime']
        self._raw_bars.index = pd.to_datetime(self._raw_bars.index, utc=True)
        self._raw_bars = {"~": self._raw_bars}

        #self._trading_hours = pd.DataFrame(columns=['opening', 'closing'])
        self._trading_hours = [now, now] # Market close
        self._trading_hours = {"~": self._trading_hours}
        self.contracts = [[""]]
        # global objects
        self.dbcurr = None
        self.dbconn = None
        self.context = None
        self.socket = None
        self.ibConn = None

        self.symbol_ids = {}  # cache
        self.cash_ticks = cash_ticks  # outside cache
        self.rtvolume = set()  # has RTVOLUME?

        self.args = {arg: val for arg, val in locals().items(
        ) if arg not in ('__class__', 'self', 'kwargs')}
        self.args.update(kwargs)

        if 'blotter' in sys.argv[0]:
            # override args with any (non-default) command-line args
            self.args.update(self.load_cli_args())




        # -------------------------------

        # last_bar_datetime
        if 'barsize' not in self.args:
             self.barsize = barsize
        else:
            self.barsize = int(self.args['barsize'])

        self.last_bar_datetime = now #+ timedelta(minutes=self.barsize)
        self.last_bar_datetime  = self.last_bar_datetime .replace(minute= (self.last_bar_datetime.minute // self.barsize) * self.barsize,
                                       second = 0,
                                       microsecond =0)
        self.last_bar_datetime = {'min' : self.last_bar_datetime,
                                  'hour': now.replace(minute=0,
                                                      second = 0,
                                                      microsecond =0),
                                  'day' : now.replace(hour=0,
                                                      minute=0,
                                                      second = 0,
                                                      microsecond =0)
                                    }

        self.bar_size = {'min' : timedelta(minutes=self.barsize),
                        'hour' : timedelta(hours=1),
                        'day' : timedelta(days=1)}

        #self.last_bar_datetime = {"~":   self.last_bar_datetime}
        print('Next valid bar at %s' % self.last_bar_datetime['min'] )


        # read cached args to detect duplicate blotters
        self.duplicate_run = False
        self.cahced_args = {}
        self.args_cache_file = "%s/%s.qtpylib" % (
            tempfile.gettempdir(), self.name)
        if os.path.exists(self.args_cache_file):
            self.cahced_args = self._read_cached_args()

        # don't display connection errors on ctrl+c
        self.quitting = False

        # do stuff on exit
        atexit.register(self._on_exit)

        # track historical data download status
        self.backfilled = False
        self.backfilled_symbols = []
        self.backfill_resolution = "1 min"

        # be aware of thread count
        self.threads = asynctools.multitasking.getPool(__name__)['threads']
        print("Number of threads :")
        print(self.threads)
    # -------------------------------------------
    def _on_exit(self, terminate=True):
        if "as_client" in self.args:
            return

        self.log_blotter.info("Blotter stopped...")

        if self.ibConn is not None:
            self.log_blotter.info("Cancel market data...")
            self.ibConn.cancelMarketData()

            self.log_blotter.info("Disconnecting...")
            self.ibConn.disconnect()

        if not self.duplicate_run:
            self.log_blotter.info("Deleting runtime args...")
            self._remove_cached_args()

        if not self.args['dbskip']:
            self.log_blotter.info("Disconnecting from MySQL...")
            try:
                self.dbcurr.close()
                self.dbconn.close()
            except Exception as e:
                pass

        if terminate:
            os._exit(0)

    # -------------------------------------------
    @staticmethod
    def _detect_running_blotter(name):
        return name

    # -------------------------------------------
    @staticmethod
    def _blotter_file_running():
        try:
            # not sure how this works on windows...
            command = 'pgrep -f ' + sys.argv[0]
            print(command)
            process = subprocess.Popen(
                command, shell=True, stdout=subprocess.PIPE)
            stdout_list = process.communicate()[0].decode('utf-8').split("\n")
            stdout_list = list(filter(None, stdout_list))
            print(sdout_list)
            return len(stdout_list) > 0
        except Exception as e:
            return False

    # -------------------------------------------
    def _check_unique_blotter(self):
        if os.path.exists(self.args_cache_file):
            # temp file found - check if really running
            # or if this file wasn't deleted due to crash
            if not self._blotter_file_running():
                # print("REMOVING OLD TEMP")
                self._remove_cached_args()
            else:
                self.duplicate_run = True
                self.log_blotter.error("Blotter is already running...")
                sys.exit(1)

        self._write_cached_args()

    # -------------------------------------------
    def _remove_cached_args(self):
        if os.path.exists(self.args_cache_file):
            os.remove(self.args_cache_file)

    def _read_cached_args(self):
        if os.path.exists(self.args_cache_file):
            return pickle.load(open(self.args_cache_file, "rb"))
        return {}

    def _write_cached_args(self):
        pickle.dump(self.args, open(self.args_cache_file, "wb"))
        tools.chmod(self.args_cache_file)

    # -------------------------------------------
    def load_cli_args(self):
        parser = argparse.ArgumentParser(
            description='QTPyLib Blotter',
            formatter_class=argparse.ArgumentDefaultsHelpFormatter)
        parser.add_argument('--name', default=None,
                    help='Name of the blotter', required=False)
        parser.add_argument('--symbols', default=self.args['symbols'],
                            help='IB contracts CSV database', required=False)
        parser.add_argument('--ibport', default=self.args['ibport'],
                            help='TWS/GW Port to use', required=False)
        parser.add_argument('--ibclient', default=self.args['ibclient'],
                            help='TWS/GW Client ID', required=False)
        parser.add_argument('--ibserver', default=self.args['ibserver'],
                            help='IB TWS/GW Server hostname', required=False)
        parser.add_argument('--zmqport', default=self.args['zmqport'],
                            help='ZeroMQ Port to use', required=False)
        parser.add_argument('--orderbook', action='store_true',
                            help='Get Order Book (Market Depth) data',
                            required=False)
        parser.add_argument('--dbhost', default=self.args['dbhost'],
                            help='MySQL server hostname', required=False)
        parser.add_argument('--dbport', default=self.args['dbport'],
                            help='MySQL server port', required=False)
        parser.add_argument('--dbname', default=self.args['dbname'],
                            help='MySQL server database', required=False)
        parser.add_argument('--dbuser', default=self.args['dbuser'],
                            help='MySQL server username', required=False)
        parser.add_argument('--dbpass', default=self.args['dbpass'],
                            help='MySQL server password', required=False)
        parser.add_argument('--dbskip', default=self.args['dbskip'],
                            required=False, help='Skip MySQL logging (flag)',
                            action='store_true')
        parser.add_argument('--barsize', default=1,
                    required=False, help='Aggregation size of Bar (min)')

        # only return non-default cmd line args
        # (meaning only those actually given)
        cmd_args, _ = parser.parse_known_args()
        args = {arg: val for arg, val in vars(
            cmd_args).items() if val != parser.get_default(arg)}
        return args

    # -------------------------------------------
    def ibCallback(self, caller, msg, **kwargs):


        if caller == "handleConnectionClosed":
            self.log_blotter.info("Lost conncetion to Interactive Brokers...")
            self._on_exit(terminate=False)
            self.run()


        elif caller == "handleContractDetails":
            self.on_contract_details_received(msg.contractDetails)


        elif caller == "handleHistoricalData":
            if msg and hasattr(msg, 'reqId'):
                if msg.reqId :

                    symbol = self.ibConn.tickerSymbol(msg.reqId)
                    if symbol not in [contract[0] for contract in self.contracts]:
                        print("symbol %s is not followed in the list :"%symbol)
                        print([contract[0] for contract in self.contracts])

                        return
                else:
                    return


            self.on_ohlc_received(msg, kwargs)

        elif caller == "handleTickString":
            self.on_tick_string_received(msg.tickerId, kwargs)

        elif caller == "handleTickPrice" or caller == "handleTickSize":
            self.on_quote_received(msg.tickerId)

        elif caller in "handleTickOptionComputation":
            self.on_option_computation_received(msg.tickerId)

        elif caller == "handleMarketDepth":
            self.on_orderbook_received(msg.tickerId)

        elif caller == "handleError":
            # don't display connection errors on ctrl+c
            if self.quitting and \
                    msg.errorCode in ibDataTypes["DISCONNECT_ERROR_CODES"]:
                return

            # errorCode can be None...
            if 1100 <= msg.errorCode < 2200 or msg.errorCode == 0:
                self.log_blotter.warning(
                    '[IB #%d] %s', msg.errorCode, msg.errorMsg)
            elif msg.errorCode not in (502, 504):  # connection error
                self.log_blotter.error(
                    '[IB #%d] %s', msg.errorCode, msg.errorMsg)

    # -------------------------------------------

    @asynctools.multitasking.task
    def on_contract_details_received(self, msg):

        """
        print(vars(msg)['m_liquidHours'])
        print(msg.m_liquidHours)
        print(dir(msg))
        """
        symbol = msg.m_summary['m_symbol']
        print("Inside on_contract_details_received : %s"%symbol)
        now = datetime.now()

        if symbol not in self._trading_hours:
            #m_liquidHours = ['%s:CLOSE' %datetime.now().strftime("%Y%m%d")] ##self.trading_hours['~']
            m_liquidHours = []
            _trading_hours = [now, now]

        if hasattr(msg, 'm_liquidHours'):
            m_liquidHours = msg.m_liquidHours.split(';')
            _trading_hours = [now, now]

        """
        # try to fetch opening table
        sql = "SELECT open, close FROM opening WHERE DATE(datetime) = '%s' AND symbol_id = '%s'"%(now.date(),symbol)
        self.dbcurr.execute(sql)
        m_liquidHours_db = self.dbcurr.fetchone()
        print("/"*10)
        print(m_liquidHours_db)
        """
        list_liquidHours = []
        for lh in m_liquidHours:
            if 'CLOSED' in lh:
                h_close = datetime.strptime(lh.split(':')[0],  "%Y%m%d")
                h_open = h_close
                list_liquidHours.append([h_open, h_close])
            else :

                h_open, h_close = lh.split("-")
                h_open = datetime.strptime(h_open, "%Y%m%d:%H%M")
                h_close = datetime.strptime(h_close, "%Y%m%d:%H%M")
                list_liquidHours.append([h_open,h_close ])

            if now.date() == h_close.date() :
                _trading_hours = [h_open, h_close]
        #print(list_liquidHours)

        self._trading_hours[symbol] = _trading_hours

        # Update _trading_hours
        data = {
            "symbol": symbol,
            "asset_class": 'STK', # should be contained in msg ...
            "m_liquidHours" : list_liquidHours[0:3], # today and tomorrow
            "timestamp" : now
                }
        #print([contract[0] for contract in self.contracts])
        if symbol in [contract[0] for contract in self.contracts]:
            self.log2db(data, 'OPENING')

    # -------------------------------------------
    def on_ohlc_received(self, msg, kwargs):
        symbol = self.ibConn.tickerSymbol(msg.reqId)

        if kwargs["completed"]:
            print('Completed : msg = %s'%msg)
            self.backfilled  = True
            self.backfilled_symbols.append(symbol)
            tickers = set(
                {v: k for k, v in self.ibConn.tickerIds.items() if v.upper() != "SYMBOL"}.keys())
            if tickers == set(self.backfilled_symbols):
                self.backfilled = True

            try:
                self.ibConn.cancelHistoricalData(
                    self.ibConn.contracts[msg.reqId])
            except Exception as e:
                print(e)
                pass

        else:
            try:
                timestamp = datetime.strptime(
                    msg.date, "%Y%m%d").strftime("%Y-%m-%d %H:%M:%S")
            except ValueError:

                timestamp = datetime.fromtimestamp(
                    int(msg.date)).replace(
                    tzinfo=None).strftime("%Y-%m-%d %H:%M:%S")

            print(timestamp)
            data = {
                "symbol": symbol,
                "symbol_group": tools.gen_symbol_group(symbol),
                "asset_class": tools.gen_asset_class(symbol),
                "timestamp": timestamp,
            }

            # incmoing second data
            if "sec" in self.backfill_resolution:
                data["last"] = tools.to_decimal(msg.close)
                data["lastsize"] = int(msg.volume)  # msg.count?
                data["bid"] = 0
                data["bidsize"] = 0
                data["ask"] = 0
                data["asksize"] = 0
                data["kind"] = "TICK"
            else:
                data["open"] = tools.to_decimal(msg.open)
                data["high"] = tools.to_decimal(msg.high)
                data["low"] = tools.to_decimal(msg.low)
                data["close"] = tools.to_decimal(msg.close)
                data["volume"] = int(msg.volume)
                data["kind"] = "BAR"
                data["historical"] = True
                data["granularity"] = self.granularity
                print(data)

            # store in db
            self.log2db(data, data["kind"])

    # -------------------------------------------

    @asynctools.multitasking.task
    def on_tick_string_received(self, tickerId, kwargs):

        # kwargs is empty
        if not kwargs:
            return

        data = None
        symbol = self.ibConn.tickerSymbol(tickerId)

        # for instruments that receive RTVOLUME events
        if "tick" in kwargs:
            self.rtvolume.add(symbol)
            data = {
                # available data from ib
                "symbol":       symbol,
                "symbol_group": tools.gen_symbol_group(symbol),  # ES_F, ...
                "asset_class":  tools.gen_asset_class(symbol),
                "timestamp":    kwargs['tick']['time'],
                "last":         tools.to_decimal(kwargs['tick']['last']),
                "lastsize":     int(kwargs['tick']['size']),
                "bid":          tools.to_decimal(kwargs['tick']['bid']),
                "ask":          tools.to_decimal(kwargs['tick']['ask']),
                "bidsize":      int(kwargs['tick']['bidsize']),
                "asksize":      int(kwargs['tick']['asksize']),
                # "wap":          kwargs['tick']['wap'],
            }

        # for instruments that DOESN'T receive RTVOLUME events (exclude options)
        elif symbol not in self.rtvolume and \
                self.ibConn.contracts[tickerId].m_secType not in ("OPT", "FOP"):

            tick = self.ibConn.marketData[tickerId]

            if not tick.empty and tick['last'].values[-1] > 0 < tick['lastsize'].values[-1]:
                data = {
                    # available data from ib
                    "symbol":       symbol,
                    # ES_F, ...
                    "symbol_group": tools.gen_symbol_group(symbol),
                    "asset_class":  tools.gen_asset_class(symbol),
                    "timestamp":    tick.index.values[-1],
                    "last":         tools.to_decimal(tick['last'].values[-1]),
                    "lastsize":     int(tick['lastsize'].values[-1]),
                    "bid":          tools.to_decimal(tick['bid'].values[-1]),
                    "ask":          tools.to_decimal(tick['ask'].values[-1]),
                    "bidsize":      int(tick['bidsize'].values[-1]),
                    "asksize":      int(tick['asksize'].values[-1]),
                    # "wap":          kwargs['tick']['wap'],
                }

        # proceed if data exists
        if data is not None:
            # cache last tick
            if symbol in self.cash_ticks.keys():
                if data == self.cash_ticks[symbol]:
                    return

            self.cash_ticks[symbol] = data

            # add options fields
            data = tools.force_options_columns(data)

            # print('.', end="", flush=True)
            self.on_tick_received(data)

    # -------------------------------------------
    @asynctools.multitasking.task
    def on_quote_received(self, tickerId):
        try:

            symbol = self.ibConn.tickerSymbol(tickerId)

            if self.ibConn.contracts[tickerId].m_secType in ("OPT", "FOP"):
                quote = self.ibConn.optionsData[tickerId].to_dict(orient='records')[
                    0]
                quote['type'] = self.ibConn.contracts[tickerId].m_right
                quote['strike'] = tools.to_decimal(
                    self.ibConn.contracts[tickerId].m_strike)
                quote["symbol_group"] = self.ibConn.contracts[tickerId].m_symbol + \
                    '_' + self.ibConn.contracts[tickerId].m_secType
                quote = tools.mark_options_values(quote)
            else:
                quote = self.ibConn.marketData[tickerId].to_dict(orient='records')[
                    0]
                quote["symbol_group"] = tools.gen_symbol_group(symbol)

            quote["symbol"] = symbol
            quote["asset_class"] = tools.gen_asset_class(symbol)
            quote['bid'] = tools.to_decimal(quote['bid'])
            quote['ask'] = tools.to_decimal(quote['ask'])
            quote['last'] = tools.to_decimal(quote['last'])
            quote["kind"] = "QUOTE"

            # cash markets do not get RTVOLUME (handleTickString)
            if quote["asset_class"] == "CSH":
                quote['last'] = round(
                    float((quote['bid'] + quote['ask']) / 2), 5)
                quote['timestamp'] = time.locatime().strftime("%Y-%m-%d %H:%M:%S.%f")

                # create synthetic tick
                if symbol in self.cash_ticks.keys() and quote['last'] != self.cash_ticks[symbol]:
                    self.on_tick_received(quote)
                else:
                    self.broadcast(quote, "QUOTE")

                self.cash_ticks[symbol] = quote['last']
            else:
                self.broadcast(quote, "QUOTE")

        except Exception as e:
            pass

    # -------------------------------------------
    @asynctools.multitasking.task
    def on_option_computation_received(self, tickerId):
        # try:
        symbol = self.ibConn.tickerSymbol(tickerId)

        tick = self.ibConn.optionsData[tickerId].to_dict(orient='records')[0]

        # must have values!
        for key in ('bid', 'ask', 'last', 'bidsize', 'asksize', 'lastsize',
                    'volume', 'delta', 'gamma', 'vega', 'theta'):
            if tick[key] == 0:
                return

        tick['type'] = self.ibConn.contracts[tickerId].m_right
        tick['strike'] = tools.to_decimal(
            self.ibConn.contracts[tickerId].m_strike)
        tick["symbol_group"] = self.ibConn.contracts[tickerId].m_symbol + \
            '_' + self.ibConn.contracts[tickerId].m_secType
        tick['volume'] = int(tick['volume'])
        tick['bid'] = tools.to_decimal(tick['bid'])
        tick['bidsize'] = int(tick['bidsize'])
        tick['ask'] = tools.to_decimal(tick['ask'])
        tick['asksize'] = int(tick['asksize'])
        tick['last'] = tools.to_decimal(tick['last'])
        tick['lastsize'] = int(tick['lastsize'])

        tick['price'] = tools.to_decimal(tick['price'], 2)
        tick['underlying'] = tools.to_decimal(tick['underlying'])
        tick['dividend'] = tools.to_decimal(tick['dividend'])
        tick['volume'] = int(tick['volume'])
        tick['iv'] = tools.to_decimal(tick['iv'])
        tick['oi'] = int(tick['oi'])
        tick['delta'] = tools.to_decimal(tick['delta'])
        tick['gamma'] = tools.to_decimal(tick['gamma'])
        tick['vega'] = tools.to_decimal(tick['vega'])
        tick['theta'] = tools.to_decimal(tick['theta'])

        tick["symbol"] = symbol
        tick["symbol_group"] = tools.gen_symbol_group(symbol)
        tick["asset_class"] = tools.gen_asset_class(symbol)

        tick = tools.mark_options_values(tick)

        # is this a really new tick?
        prev_last = 0
        prev_lastsize = 0
        if symbol in self.cash_ticks.keys():
            prev_last = self.cash_ticks[symbol]['last']
            prev_lastsize = self.cash_ticks[symbol]['lastsize']
            if tick == self.cash_ticks[symbol]:
                return

        self.cash_ticks[symbol] = dict(tick)

        # assign timestamp
        tick['timestamp'] = self.ibConn.optionsData[tickerId].index[0]
        if tick['timestamp'] == 0:
            tick['timestamp'] = time.localtime().strftime(
                ibDataTypes['DATE_TIME_FORMAT_LONG_MILLISECS'])

        # treat as tick if last/volume changed
        if tick['last'] != prev_last or tick['lastsize'] != prev_lastsize:
            tick["kind"] = "TICK"
            self.on_tick_received(tick)

        # otherwise treat as quote
        else:
            tick["kind"] = "QUOTE"
            self.broadcast(tick, "QUOTE")

        # except Exception as e:
            # pass

    # -------------------------------------------
    @asynctools.multitasking.task
    def on_orderbook_received(self, tickerId):
        orderbook = self.ibConn.marketDepthData[tickerId].dropna(
            subset=['bid', 'ask']).fillna(0).to_dict(orient='list')

        # add symbol data to list
        symbol = self.ibConn.tickerSymbol(tickerId)
        orderbook['symbol'] = symbol
        orderbook["symbol_group"] = tools.gen_symbol_group(symbol)
        orderbook["asset_class"] = tools.gen_asset_class(symbol)
        orderbook["kind"] = "ORDERBOOK"

        # broadcast
        self.broadcast(orderbook, "ORDERBOOK")
    # -------------------------------------------

    @asynctools.multitasking.task
    def on_tick_received(self, tick):
        # data
        #self.log_blotter.info('counter : %s'%self.counter)

        symbol = tick['symbol']
        #self.log_blotter.info("In on_tick_received, symbol %s"%symbol)

        timestamp = datetime.strptime(tick['timestamp'],
                                      ibDataTypes["DATE_TIME_FORMAT_LONG_MILLISECS"])

        # do not act on first tick (timezone is incorrect)
        if self.first_tick:
            self.first_tick = False
            return

        try:
            timestamp = parse_date(timestamp)
        except Exception as e:
            pass
        # placeholders
        """
        if symbol not in self._raw_bars:
            self._raw_bars[symbol] = self._raw_bars['~']

        if symbol not in self._bars:
            self._bars[symbol] = self._bars['~']

        """

        #self.log_blotter.info('symbol : %s'%symbol)

        # send tick to message self.broadcast
        tick["kind"] = "TICK"
        self.broadcast(tick, "TICK")
        #self.log2db(tick, "TICK")

        # add tick to self._raw_bars
        tick_data = pd.DataFrame(index=['timestamp'],
                                 data={'timestamp': timestamp,
                                       'last': tick['last'],
                                       'volume': tick['lastsize'],
                                       'symbol_group' : tick['symbol_group'],
                                       'asset_class' : tick['asset_class']})

        tick_data.set_index(['timestamp'], inplace=True)
        #self.log_blotter.info("tick_data")
        #self.log_blotter.info(tick_data)

        #self._raw_bars[symbol] = self._raw_bars[symbol].append(tick_data)
        #self.log_blotter.info("self._raw_bars[symbol] ")
        #self.log_blotter.info(self._raw_bars[symbol] )

        bar = {'timestamp': timestamp.replace(
                                       minute= (timestamp.minute // self.barsize) * self.barsize,
                                       second = 0,
                                       microsecond =0),
              'symbol' : symbol,
              'asset_class' :  tick['asset_class'],
              'open': tick['last'],
              'close': tick['last'],
              'high': tick['last'],
              'low': tick['last'],
              'volume': tick['lastsize'],
              'granularity' : "min",
              'kind' : 'BAR'
              }


        self.log2db(bar, "BAR")

        bar.update({'timestamp': timestamp.replace(
                                       hour = timestamp.hour ,
                                       minute =0,
                                       second = 0,
                                       microsecond =0),
                    'granularity' : "hour"
                    })

        self.log2db(bar, "BAR")

        bar.update({'timestamp': timestamp.replace(
                                   day = timestamp.day,
                                   hour = 0 ,
                                   minute =0,
                                   second = 0,
                                   microsecond =0),
                'granularity' : "day"
                })

        self.log2db(bar, "BAR")

        bar.update({'timestamp': (timestamp - timedelta(days=timestamp.weekday())).replace(
                                       hour = 0 ,
                                       minute =0,
                                       second = 0,
                                       microsecond =0),
                    'granularity' : "week"
                        })

        self.log2db(bar, "BAR")
    # -------------------------------------------

    @asynctools.multitasking.task
    def new_bar(self, symbol, last_bar_datetime, granularity):

        #Wait a lag after the end building bar and send the bar
        #print("Trhread safe")

        #print(self._raw_bars)
        bar = {}
        bar["symbol"] = symbol
        bar["asset_class"] = 'STK'
        bar["timestamp"] = last_bar_datetime.strftime(
            ibDataTypes["DATE_TIME_FORMAT_LONG"])

        #self.log_blotter.info(bar)
        bar["kind"] = "BAR"
        bar["granularity"] = granularity
        bar["missing"] = True

        self.log2db(bar, "BAR")
        self.broadcast(bar, "BAR")




        return

    # -------------------------------------------

    def check_new_bar(self, contracts, now, granularity):

        last_bar_datetime = self.last_bar_datetime[granularity]
        lag = 1
        print('now           : %s '%now)
        print('last  %s    : %s'%(granularity, last_bar_datetime))

        if (now - last_bar_datetime) > self.bar_size[granularity] + timedelta(seconds=lag) :

            contract_open = []
            for contract in contracts:
                time.sleep(0.01)
                contract = contract[0]
                if contract not in self._trading_hours :
                    self.log_blotter.info("Here trading hour is : %s"%self._trading_hours)
                    self._trading_hours[contract] = self._trading_hours['~']

                print(last_bar_datetime, self._trading_hours[contract])
                # test market open/close :
                if (last_bar_datetime >= self._trading_hours[contract][0])  and (last_bar_datetime < self._trading_hours[contract][1]) :
                    self.log_blotter.info('Market is open for contract %s '%contract)
                    # non blocking
                    contract_open +=  [contract]
                    if granularity in ["min", "hour"]:
                        self.new_bar(contract, last_bar_datetime, granularity)

                else:
                    self.log_blotter.info('Market is close for contract %s '%contract)

                #contract_open +=  [contract]

            # cron signal to ping all stacked service
            if granularity == "min":
                self.broadcast({'kind' : 'CRON', 'name' : self.name}, "CRON")

            """
            if granularity == "min" and len(contract_open)>0:
                ### Send syncrone trigger for all contracts
                bar = {}
                bar["cron"] = True
                bar["symbol"] = contract_open
                #bar['trading_hours'] = self._trading_hours
                bar["asset_class"] = 'STK'
                bar["timestamp"] = last_bar_datetime.strftime(
                    ibDataTypes["DATE_TIME_FORMAT_LONG"])

                #self.log_blotter.info(bar)
                bar["kind"] = "BAR"
                bar["granularity"] = granularity
                self.broadcast(bar, "BAR")
            """
            self.last_bar_datetime[granularity] = last_bar_datetime + self.bar_size[granularity]
            return True
        else:
            print('accumulation ...')
            return False
    # -------------------------------------------

    def broadcast(self, data, kind):
        def int64_handler(o):
            if isinstance(o, np_int64):
                try:
                    return pd.to_datetime(o, unit='ms').strftime(
                        ibDataTypes["DATE_TIME_FORMAT_LONG"])
                except Exception as e:
                    return int(o)
            raise TypeError

        string2send = "%s %s" % (
            self.args["zmqtopic"], json.dumps(data, default=int64_handler))

        try:
            self.socket.send_string(string2send)
        except Exception as e:
            print('Broadcast error : ')
            print(e)
            pass

    # -------------------------------------------
    @timing
    def log2db(self, data, kind):
        if self.args['dbskip'] or len(data["symbol"].split("_")) > 2:
            return
        self.threads = 1
        # connect to mysql per call (thread safe)
        if self.threads > 0:
            dbconn = self.get_mysql_connection()
            dbcurr = dbconn.cursor()
        else:
            dbconn = self.dbconn
            dbcurr = self.dbcurr

        # set symbol details
        symbol_id = 0
        symbol = data["symbol"].replace("_" + data["asset_class"], "")

        if symbol in self.symbol_ids.keys():
            symbol_id = self.symbol_ids[symbol]
        else:
            symbol_id = get_symbol_id(
                data["symbol"], dbconn, dbcurr, self.ibConn)
            self.symbol_ids[symbol] = symbol_id

        # insert to db
        if kind == "TICK":
            try:
                mysql_insert_tick(data, symbol_id, dbcurr)
            except Exception as e:
                print('Cannot insert TICK')
                print(e)
                print(data)
                print(symbol_id)

        elif kind == "BAR" :
            try:
                mysql_insert_bar(data, symbol_id, dbcurr)
            except Exception as e:
                print(e)
                print(data)
                self.log_blotter.info('Cannot insert BAR')


        elif kind == "OPENING" :
            try:
                mysql_insert_opening(data, symbol_id, dbcurr)
            except Exception as e:
                print('Cannot insert OPENING')
                print(e)

        # commit
        try:
            dbconn.commit()
        except Exception as e:
            print("Cannot commit")
            print(e)


        # disconect from mysql
        if self.threads > 0:
            dbcurr.close()
            dbconn.close()
    # ---------------------------------------
    def initiate_socket(self):

        self.context = zmq.Context(zmq.REP)
        self.socket = self.context.socket(zmq.PUB)
        print("PUB to port %s"%self.args['zmqport'])
        self.socket.bind("tcp://*:" + str(self.args['zmqport']))

    # -------------------------------------------
    def run(self):
        """Starts the blotter

        Connects to the TWS/GW, processes and logs market data,
        and broadcast it over TCP via ZeroMQ (which algo subscribe to)
        """

        self._check_unique_blotter()

        # connect to mysql
        self.mysql_connect()

        self.initiate_socket()

        db_modified = 0
        contracts = []
        prev_contracts = []
        first_run = True
        new_hour, new_day = False, False

        self.log_blotter.info("Connecting to Interactive Brokers...")
        self.ibConn = ezIBpy()
        self.ibConn.ibCallback = self.ibCallback

        while not self.ibConn.connected:
            self.ibConn.connect(clientId=int(self.args['ibclient']),
                                port=int(self.args['ibport']), host=str(self.args['ibserver']))
            time.sleep(1)
            if not self.ibConn.connected:
                print('*', end="", flush=True)
        self.log_blotter.info("Connection established...")

        try:
            while True:

                if not os.path.exists(self.args['symbols']):
                    pd.DataFrame(columns=['symbol', 'sec_type', 'exchange',
                                          'currency', 'expiry', 'strike', 'opt_type']
                                 ).to_csv(self.args['symbols'], header=True, index=False)
                    tools.chmod(self.args['symbols'])
                else:
                    time.sleep(0.1)

                    # read db properties
                    db_data = os.stat(self.args['symbols'])
                    db_size = db_data.st_size
                    db_last_modified = db_data.st_mtime

                    # empty file
                    if db_size == 0:
                        if prev_contracts:
                            self.log_blotter.info('Cancel market data...')
                            self.ibConn.cancelMarketData()
                            time.sleep(0.1)
                            prev_contracts = []
                        continue

                    # modified?
                    if not first_run and db_last_modified == db_modified:
                        continue

                    # continue...
                    db_modified = db_last_modified

                    # read contructs db
                    df = pd.read_csv(self.args['symbols'], header=0)
                    if df.empty:
                        continue

                    # removed expired
                    df = df[(
                            (df['expiry'] < 1000000) & (
                                df['expiry'] >= int(datetime.now().strftime('%Y%m')))) | (
                            (df['expiry'] >= 1000000) & (
                                df['expiry'] >= int(datetime.now().strftime('%Y%m%d')))) |
                            np_isnan(df['expiry'])
                            ]

                    # fix expiry formatting (no floats)
                    df['expiry'] = df['expiry'].fillna(
                        0).astype(int).astype(str)
                    df.loc[df['expiry'] == "0", 'expiry'] = ""
                    df = df[df['sec_type'] != 'BAG']

                    df.fillna("", inplace=True)
                    df.to_csv(self.args['symbols'], header=True, index=False)
                    tools.chmod(self.args['symbols'])

                    # ignore commentee
                    df = df[~df['symbol'].str.contains("#")]
                    self.contracts = [tuple(x) for x in df.values]

                    if first_run:
                        first_run = False

                    else:
                        if self.contracts  != prev_contracts:
                            # cancel market data for removed contracts
                            for contract in prev_contracts:
                                if contract not in self.contracts :
                                    self.ibConn.cancelMarketData(
                                        self.ibConn.createContract(contract))
                                    if self.args['orderbook']:
                                        print("ORER BOOK ASKED !!!")
                                        self.ibConn.cancelMarketDepth(
                                            self.ibConn.createContract(contract))
                                    time.sleep(0.1)
                                    contract_string = self.ibConn.contractString(
                                        contract).split('_')[0]
                                    self.log_blotter.info(
                                        'Contract Removed [%s]', contract_string)

                    # request market data
                    for contract in self.contracts:
                        #print(self.ibConn.contractDetails(contract[0]))

                        if contract not in prev_contracts:

                            self.ibConn.requestMarketData(
                                self.ibConn.createContract(contract))
                            if self.args['orderbook']:
                                self.ibConn.requestMarketDepth(
                                    self.ibConn.createContract(contract))
                            time.sleep(0.1)
                            contract_string = self.ibConn.contractString(
                                contract).split('_')[0]
                            self.log_blotter.info(
                                'Contract Added [%s]', contract_string)


                    now = datetime.now()

                    new_min = self.check_new_bar(self.contracts, now, 'min')

                    if new_min :
                        new_hour = self.check_new_bar(self.contracts, now, 'hour')

                    if new_hour:
                        new_day = self.check_new_bar(self.contracts, now, 'day')

                    if new_day:

                        # update self_trading_hours every day for each contract

                        #  blocking
                        for contract in self.contracts:
                            self.ibConn.requestContractDetails(
                            self.ibConn.createContract(contract))


                        """
                        # drop ticks of last day
                        print('**** DROP ticks of past day *****')
                        self.dbcurr.execute("DELETE FROM ticks WHERE DATE(datetime) != '%s'"%self.last_bar_datetime['day'].strftime("%Y-%m-%d"))
                        """



                    # update latest contracts
                    prev_contracts = self.contracts



                time.sleep(2)

        except (KeyboardInterrupt, SystemExit):
            self.quitting = True  # don't display connection errors on ctrl+c
            print(
                "\n\n>>> Interrupted with Ctrl-c...\n(waiting for running tasks to be completed)\n")
            # asynctools.multitasking.killall() # stop now
            asynctools.multitasking.wait_for_tasks()  # wait for threads to complete
            sys.exit(1)

    # -------------------------------------------
    def stream(self, symbols, tick_handler=None, bar_handler=None,
               quote_handler=None, book_handler=None,
               tunnel_handler=None, strategy_handler=None,overshoot_handler=None,
               cron_handler=None,
               contract_restriction=True, zmqport_list=[]):
        # load runtime/default data
        if isinstance(symbols, str):
            symbols = symbols.split(',')
        symbols = list(map(str.strip, symbols))
        print("We follow those symbols %s" %symbols)
        # connect to zeromq self.socket
        self.context = zmq.Context()
        sock = self.context.socket(zmq.SUB)
        sock.setsockopt_string(zmq.SUBSCRIBE, "")
        if len(zmqport_list) == 0:
            zmqport_list = [self.args['zmqport']] # connect to blotter by default
        for zmqport in zmqport_list:
            print('listen port %s'% zmqport)
            sock.connect('tcp://127.0.0.1:' + str(zmqport))

        try:
            while True:

                message = sock.recv_string()
                #print("message is %s"%message)
                if self.args["zmqtopic"] in message:
                    message = message.split(self.args["zmqtopic"])[1].strip()
                    data = json.loads(message)

                    if data['kind'] == "CRON":
                        if cron_handler is not None:
                            cron_handler(data)
                            continue

                    # TODO : There is a lot of quote!!
                    if contract_restriction and data['symbol'] not in symbols:
                        print("%s not in list" %data['symbol'])
                        continue

                    # convert None to np.nan !!
                    data.update((k, np_nan)
                                for k, v in data.items() if v is None)

                    # quote
                    if data['kind'] == "ORDERBOOK":
                        if book_handler is not None:
                            book_handler(data)
                            continue
                    # quote
                    elif data['kind'] == "QUOTE":
                        if quote_handler is not None:
                            quote_handler(data)
                            continue

                    elif data['kind'] == "TICK":
                        if tick_handler is not None:
                            tick_handler(data)
                            continue
                    elif data['kind'] == "BAR":
                        if bar_handler is not None:
                            bar_handler(data)
                            continue

                    elif data['kind'] == "TUNNEL":
                        if tunnel_handler is not None:
                            tunnel_handler(data)
                            continue

                    elif data['kind'] == "OVERSHOOT":
                        if tunnel_handler is not None:
                            overshoot_handler(data)
                            continue


        except (KeyboardInterrupt, SystemExit):
            print(
                "\n\n>>> Interrupted with Ctrl-c...\n(waiting for running tasks to be completed)\n")
            print(".\n.\n.\n")
            # asynctools.multitasking.killall() # stop now
            asynctools.multitasking.wait_for_tasks()  # wait for threads to complete
            sys.exit(1)

    # -------------------------------------------
    @staticmethod
    def drip(data, handler):
        try:
            for i in range(len(data)):
                handler(data.iloc[i:i + 1])
                time.sleep(.15)

            asynctools.multitasking.wait_for_tasks()
            print("\n\n>>> Backtesting Completed.")

        except (KeyboardInterrupt, SystemExit):
            print(
                "\n\n>>> Interrupted with Ctrl-c...\n(waiting for running tasks to be completed)\n")
            print(".\n.\n.\n")
            # asynctools.multitasking.killall() # stop now
            asynctools.multitasking.wait_for_tasks()  # wait for threads to complete
            sys.exit(1)

    # ---------------------------------------
    def backfill(self, data, resolution, start, end=None, contract = []):
        """
        Backfills missing historical data

        :Optional:
            data : pd.DataFrame
                Minimum required bars for backfill attempt
            resolution : str
                Algo resolution
            start: datetime
                Backfill start date (YYYY-MM-DD [HH:MM:SS[.MS]).
            end: datetime
                Backfill end date (YYYY-MM-DD [HH:MM:SS[.MS]). Default is None
        :Returns:
            status : mixed
                False for "won't backfill" / True for "backfilling, please wait"
        """

        data.sort_index(inplace=True)


        # missing history?
        start_date = parse_date(start)
        end_date = parse_date(end) if end else datetime.now()

        if data.empty:
            first_date = datetime.now()
            last_date = datetime.now()
        else:
            first_date = tools.datetime64_to_datetime(data.index.values[0])
            last_date = tools.datetime64_to_datetime(data.index.values[-1])


        ib_lookback = None
        if start_date < first_date:
            ib_lookback = tools.ib_duration_str(start_date)
        #elif end_date > last_date:
        #    ib_lookback = tools.ib_duration_str(last_date)

        if not ib_lookback:
            self.backfilled = True
            return None


        if 'H' in resolution:
            self.backfill_resolution = '1 hour'
            self.granularity = 'hour'
        elif 'W' in resolution:
            self.backfill_resolution = '1 week'
            self.granularity = 'week'
        elif 'D' in resolution:
            self.backfill_resolution = '1 day'
            self.granularity = 'day'
        elif 'T' in resolution :
            self.backfill_resolution = '5 mins'
            self.granularity = 'min'

        self.log_blotter.warning("Backfilling historical data from IB...")

            # request parameters
        params = {
            "lookback": ib_lookback,
            "resolution": self.backfill_resolution,
            "data": "TRADES",
            "rth": False,
            "end_datetime": None,
            "csv_path": None
        }
        print(params)
        # if connection is active - request data
        if len(contract)>0:
            self.ibConn.requestHistoricalData(contracts = contract,**params)
        else: # Request  history for all contract created
            self.ibConn.requestHistoricalData(**params)

        # wait for backfill to complete
        while not self.backfilled:
            time.sleep(0.01)

        # otherwise, pass the parameters to the caller
        return True

    # -------------------------------------------
    def register(self, instruments):

        if isinstance(instruments, dict):
            instruments = list(instruments.values())

        if not isinstance(instruments, list):
            return

        db = pd.read_csv(self.args['symbols'], header=0).fillna("")

        instruments = pd.DataFrame(instruments)
        instruments.columns = db.columns
        # instruments['expiry'] = instruments['expiry'].astype(int).astype(str)

        db = db.append(instruments)
        # db['expiry'] = db['expiry'].astype(int)
        db = db.drop_duplicates(keep="first")

        db.to_csv(self.args['symbols'], header=True, index=False)
        tools.chmod(self.args['symbols'])

    # -------------------------------------------
    def get_mysql_connection(self):
        if self.args['dbskip']:
            return None

        return pymysql.connect(
            client_flag=MULTI_STATEMENTS,
            host=str(self.args['dbhost']),
            port=int(self.args['dbport']),
            user=str(self.args['dbuser']),
            passwd=str(self.args['dbpass']),
            db=str(self.args['dbname'])
        )

    def mysql_connect(self):

        # skip db connection
        if self.args['dbskip']:
            return

        # already connected?
        if self.dbcurr is not None or self.dbconn is not None:
            return

        # connect to mysql
        self.dbconn = self.get_mysql_connection()
        self.dbcurr = self.dbconn.cursor()

        # check for db schema
        self.dbcurr.execute("SHOW TABLES")
        tables = [table[0] for table in self.dbcurr.fetchall()]

        required = ["bars_min", "ticks", "symbols",
                    "trades", "greeks", "_version_"]
        if all(item in tables for item in required):
            self.dbcurr.execute("SELECT version FROM `_version_`")
            db_version = self.dbcurr.fetchone()
            if db_version is not None and __version__ == db_version[0]:
                return

        # create database schema
        print('*'*10)
        print(path['library'])
        self.dbcurr.execute(open(path['library'] + '/schema.sql', "rb").read())
        try:
            self.dbconn.commit()

            # update version #
            sql = "TRUNCATE TABLE _version_; INSERT INTO _version_ (`version`) VALUES (%s)"
            self.dbcurr.execute(sql, (__version__))
            self.dbconn.commit()

            # unless we do this, there's a problem with curr.fetchX()
            self.dbcurr.close()
            self.dbconn.close()

            # re-connect to mysql
            self.dbconn = self.get_mysql_connection()
            self.dbcurr = self.dbconn.cursor()

        except Exception as e:
            self.dbconn.rollback()
            self.log_blotter.error("Cannot create database schema")
            self._remove_cached_args()
            sys.exit(1)

    # ===========================================
    # Utility functions --->
    # ===========================================

    # -------------------------------------------


# -------------------------------------------
def load_blotter_args(blotter_name=None, logger=None):
    """ Load running blotter's settings (used by clients)

    :Parameters:
        blotter_name : str
            Running Blotter's name (defaults to "auto-detect")
        logger : object
            Logger to be use (defaults to Blotter's)

    :Returns:
        args : dict
            Running Blotter's arguments
    """
    if logger is None:
        logger = tools.createLogger(__name__, logging.WARNING)

    # find specific name
    if blotter_name is not None:  # and blotter_name != 'auto-detect':
        args_cache_file = tempfile.gettempdir() + "/" + blotter_name.lower() + ".qtpylib"
        print("Read blotter %s"%args_cache_file)
        logger.info("Read blotter %s"%args_cache_file)
        if not os.path.exists(args_cache_file):
            logger.critical(
                "Cannot connect to running Blotter [%s]", blotter_name)
            if os.isatty(0):
                sys.exit(0)
            return []

    # no name provided - connect to last running
    else:
        blotter_files = sorted(
            glob.glob(tempfile.gettempdir() + "/*.qtpylib"), key=os.path.getmtime)

        if not blotter_files:
            logger.critical(
                "Cannot connect to running Blotter [%s]", blotter_name)
            if os.isatty(0):
                sys.exit(0)
            return []

        args_cache_file = blotter_files[-1]

    args = pickle.load(open(args_cache_file, "rb"))
    args['as_client'] = True

    return args

# -------------------------------------------


def get_symbol_id(symbol, dbconn, dbcurr, ibConn=None):
    """
    Retrives symbol's ID from the Database or create it if it doesn't exist

    :Parameters:
        symbol : str
            Instrument symbol
        dbconn : object
            Database connection to be used
        dbcurr : object
            Database cursor to be used

    :Optional:
        ibConn : object
            ezIBpy object (used for determining futures/options expiration)

    :Returns:
        symbol_id : int
            Symbol ID
    """
    def _get_contract_expiry(symbol, ibConn=None):
        # parse w/p ibConn
        if ibConn is None or isinstance(symbol, str):
            return tools.contract_expiry_from_symbol(symbol)

        # parse with ibConn
        contract_details = ibConn.contractDetails(symbol)["m_summary"]
        print("contractDetails" + "*"*10)
        print(contractDetails)
        if contract_details["m_expiry"] == "":
            ibConn.createContract(symbol)
            return _get_contract_expiry(symbol, ibConn)

        if contract_details["m_expiry"]:
            return datetime.strptime(str(contract_details["m_expiry"]), '%Y%m%d'
                                     ).strftime("%Y-%m-%d")

        return contract_details["m_expiry"]

    # start
    asset_class = tools.gen_asset_class(symbol)
    symbol_group = tools.gen_symbol_group(symbol)
    clean_symbol = symbol.replace("_" + asset_class, "")
    expiry = None

    if asset_class in ("FUT", "OPT", "FOP"):
        expiry = _get_contract_expiry(symbol, ibConn)

        # look for symbol w/ expiry
        sql = """SELECT id FROM `symbols` WHERE
            `symbol`=%s AND `symbol_group`=%s AND `asset_class`=%s  AND `expiry`=%s LIMIT 1"""
        dbcurr.execute(sql, (clean_symbol, symbol_group, asset_class, expiry))

    else:
        # look for symbol w/o expiry
        sql = """SELECT id FROM `symbols` WHERE
            `symbol`=%s AND `symbol_group`=%s AND `asset_class`=%s LIMIT 1"""
        dbcurr.execute(sql, (clean_symbol, symbol_group, asset_class))

    row = dbcurr.fetchone()

    # symbol already in db
    if row is not None:
        return row[0]

    # symbol/expiry not in db... insert new/update expiry
    else:
        # need to update the expiry?
        if expiry is not None:
            sql = """SELECT id FROM `symbols` WHERE
                `symbol`=%s AND `symbol_group`=%s AND `asset_class`=%s LIMIT 1"""
            dbcurr.execute(sql, (clean_symbol, symbol_group, asset_class))

            row = dbcurr.fetchone()
            if row is not None:
                sql = "UPDATE `symbols` SET `expiry`='" + \
                    str(expiry) + "' WHERE id=" + str(row[0])
                dbcurr.execute(sql)
                try:
                    dbconn.commit()
                except Exception as e:
                    return False
                return int(row[0])

        # insert new symbol
        sql = """INSERT IGNORE INTO `symbols`
            (`symbol`, `symbol_group`, `asset_class`, `expiry`) VALUES (%s, %s, %s, %s)
            ON DUPLICATE KEY UPDATE `symbol`=`symbol`, `expiry`=%s
        """
        dbcurr.execute(sql, (clean_symbol, symbol_group,
                             asset_class, expiry, expiry))
        try:
            dbconn.commit()
        except Exception as e:
            return False

        return dbcurr.lastrowid


# -------------------------------------------
def mysql_insert_tick(data, symbol_id, dbcurr):

    sql = """INSERT IGNORE INTO `ticks` (`datetime`, `symbol_id`,
        `bid`, `bidsize`, `ask`, `asksize`, `last`, `lastsize`)
        VALUES (%s, %s, %s, %s, %s, %s, %s, %s)
        ON DUPLICATE KEY UPDATE `symbol_id`=`symbol_id`
    """
    dbcurr.execute(sql, (data["timestamp"], symbol_id,
                         float(data["bid"]), int(data["bidsize"]),
                         float(data["ask"]), int(data["asksize"]),
                         float(data["last"]), int(data["lastsize"])
                         ))

    # add greeks
    if dbcurr.lastrowid and data["asset_class"] in ("OPT", "FOP"):
        greeks_sql = """INSERT IGNORE INTO `greeks` (
            `tick_id`, `price`, `underlying`, `dividend`mysql_insert_missing_bar, `volume`,
            `iv`, `oi`, `delta`, `gamma`, `theta`, `vega`)
            VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
        """
        try:
            dbcurr.execute(greeks_sql, (dbcurr.lastrowid,
                                        round(float(data["opt_price"]), 2), round(
                                            float(data["opt_underlying"]), 5),
                                        float(data["opt_dividend"]), int(
                                            data["opt_volume"]),
                                        float(data["opt_iv"]), float(
                                            data["opt_oi"]),
                                        float(data["opt_delta"]), float(
                                            data["opt_gamma"]),
                                        float(data["opt_theta"]), float(
                                            data["opt_vega"]),
                                        ))
        except Exception as e:
            pass


# -------------------------------------------
def mysql_insert_bar(data, symbol_id, dbcurr):

    if "missing" in data and data["missing"]:

        #dbcurr.execute("""SELECT 1 FROM bars_%s WHERE datetime = '%s' AND symbol_id = '%s'"""%(data['granularity'],data["timestamp"], symbol_id))
        #bar_exist = dbcurr.fetchone()
        #print("bar_exist :")
        #print(bar_exist)
        #if bar_exist is None:
        #    sql = """INSERT IGNORE INTO bars_{granularity} (datetime, symbol_id,open,high,low,close,volume)
        #    SELECT '{datetime}', symbol_id,close,close,close,close,0 FROM bars_{granularity}
        #    WHERE id = ( SELECT MAX(id) FROM bars_{granularity} WHERE symbol_id={symbol_id} AND datetime<{datetime});
        #    """.format(symbol_id=symbol_id, datetime=data["timestamp"], granularity = data['granularity'])

        # Insert last row at timestamp, volume 0
        sql = """INSERT IGNORE INTO bars_{granularity} (datetime, symbol_id,open,high,low,close,volume)
        SELECT '{datetime}', symbol_id,close,close,close,close,0 FROM bars_{granularity}
        WHERE id = ( SELECT MAX(id) FROM bars_{granularity} WHERE symbol_id='{symbol_id}' AND datetime<'{datetime}')
        ON DUPLICATE KEY UPDATE market=TRUE;
        """.format(symbol_id=symbol_id, datetime=data["timestamp"], granularity = data['granularity'])
        #print("bars_%s"%granularity)
        dbcurr.execute(sql)

    elif "historical" in data and data["historical"]:

        #dbcurr.execute("""SELECT 1 FROM bars_%s WHERE datetime = '%s' AND symbol_id = '%s'"""%(data['granularity'],data["timestamp"], symbol_id))
        #bar_exist = dbcurr.fetchone()
        #print("bar_exist :")
        #print(bar_exist)
        #if bar_exist is None:
        #    sql = """INSERT IGNORE INTO bars_{granularity} (datetime, symbol_id,open,high,low,close,volume)
        #    SELECT '{datetime}', symbol_id,close,close,close,close,0 FROM bars_{granularity}
        #    WHERE id = ( SELECT MAX(id) FROM bars_{granularity} WHERE symbol_id={symbol_id} AND datetime<{datetime});
        #    """.format(symbol_id=symbol_id, datetime=data["timestamp"], granularity = data['granularity'])

        # Insert last row at timestamp, volume 0
        sql = """INSERT IGNORE INTO `{}`
            (`datetime`, `symbol_id`, `open`, `high`, `low`, `close`, `volume`, `market`)
                VALUES (%s, %s, %s, %s, %s, %s, %s,%s)
            ON DUPLICATE KEY UPDATE
                 `market`=TRUE;
        """
                #print("bars_%s"%granularity)
        dbcurr.execute(sql.format("bars_%s"%data['granularity']), ( data["timestamp"], symbol_id,
                             float(data["open"]), float(data["high"]), float(
                                 data["low"]), float(data["close"]), int(data["volume"]), True
            ))

    else :

        sql = """INSERT IGNORE INTO `{}`
            (`datetime`, `symbol_id`, `open`, `high`, `low`, `close`, `volume`)
                VALUES (%s, %s, %s, %s, %s, %s, %s)
            ON DUPLICATE KEY UPDATE
                 `high`=GREATEST(`high`,%s), `low`=LEAST(`low`,%s), `close`=%s, `volume`=`volume`+%s
        """
        #print(granularity)
        #print("bars_%s"%granularity)
        dbcurr.execute(sql.format("bars_%s"%data['granularity']), ( data["timestamp"], symbol_id,
                             float(data["open"]), float(data["high"]), float(
                                 data["low"]), float(data["close"]), int(data["volume"]),
                             float(data["high"]), float(
            data["low"]), float(data["close"]), int(data["volume"])
        ))


        # add greeks
        if dbcurr.lastrowid and data["asset_class"] in ("OPT", "FOP"):
            greeks_sql = """INSERT IGNORE INTO `greeks` (
                `bar_id`, `price`, `underlying`, `dividend`, `volume`,
                `iv`, `oi`, `delta`, `gamma`, `theta`, `vega`)
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
            """
            greeks = cash_ticks[data['symbol']]
            try:
                dbcurr.execute(greeks_sql, (dbcurr.lastrowid,
                                            round(float(greeks["opt_price"]), 2), round(
                                                float(greeks["opt_underlying"]), 5),
                                            float(greeks["opt_dividend"]), int(
                                                greeks["opt_volume"]),
                                            float(greeks["opt_iv"]), float(
                                                greeks["opt_oi"]),
                                            float(greeks["opt_delta"]), float(
                                                greeks["opt_gamma"]),
                                            float(greeks["opt_theta"]), float(
                                                greeks["opt_vega"]),
                                            ))
            except Exception as e:
                pass

# -------------------------------------------
def mysql_insert_opening(data, symbol_id, dbcurr):

    sql = "SELECT open, close FROM opening WHERE DATE(datetime) = '%s' AND symbol_id = '%s'"%(data['timestamp'].date(),symbol_id)
    dbcurr.execute(sql)
    m_liquidHours_db = dbcurr.fetchone()
    #print("m_liquidHours_db")
    #print(m_liquidHours_db)
    if m_liquidHours_db is None:
    # Insert last row at timestamp, volume 0
        for h_open, h_close in data['m_liquidHours']:
            datetime = h_open.date()

            sql = """INSERT IGNORE INTO `{table}`
                (`datetime`, `symbol_id`, `open`, `close`)
                    VALUES (%s, %s, %s, %s)
                ON DUPLICATE KEY UPDATE
                      `open`=%s, `close`=%s
            """.format(table='opening',symbol_id=symbol_id, datetime=datetime)
            #print(granularity)
            #print("bars_%s"%granularity)
            dbcurr.execute(sql, (datetime, symbol_id, h_open, h_close, h_open, h_close))


# -------------------------------------------
if __name__ == "__main__":
    blotter = Blotter()
    blotter.run()
