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
import tempfile, pickle
import argparse
import inspect
import sys
import logging
import os
import ezibpy
import pymysql
import time
import json
import zmq
import re

from multiprocessing import Pool, cpu_count

from datetime import datetime
from abc import ABCMeta, abstractmethod

import pandas as pd
from numpy import nan

from qtpylib.broker import Broker
from qtpylib.workflow import validate_columns as validate_csv_columns
from qtpylib import (
    tools, sms, asynctools, slack_api
)
from qtpylib.instrument import Instrument

from qtpylib.blotter_5min import (
    Blotter, load_blotter_args, get_symbol_id
)
from ezibpy import (
    ezIBpy, dataTypes as ibDataTypes
)
from numpy import (
    isnan as np_isnan,
    nan as np_nan,
    int64 as np_int64
)
# =============================================
# check min, python version
if sys.version_info < (3, 4):
    raise SystemError("QTPyLib requires Python version >= 3.4")

# =============================================
# Configure logging
tools.createLogger(__name__)

# =============================================
# set up threading pool
__threads__ = tools.read_single_argv("--threads")
__threads__ = int(__threads__) if tools.is_number(__threads__) else None
asynctools.multitasking.createPool(__name__, __threads__)

# =============================================

class Model(Broker):
    """Model class initilizer

    :Parameters:

        instruments : list
            List of IB contract tuples. Default is empty list
        resolution : str
            Desired bar resolution (using pandas resolution: 1T, 1H, etc).
            Use K for tick bars. Default is 5T (5min)
        tick_window : int
            Length of tick lookback window to keep. Defaults to 1
        bar_window : int
            Length of bar lookback window to keep. Defaults to 100
        preload : str
            Preload history when starting algo (Pandas resolution: 1H, 1D, etc)
            Use K for tick bars.
        blotter : str
            Log events to this Blotter's MySQL (default is "auto detect")
        sms: set
            List of numbers to text orders (default: None)
        slack: bool
            Whether to send slack message  (default: False)
        channel: str
            Channel name to post (default: random)
        log: str
            Path to store event data (default: None)
        backtest: bool
            Whether to operate in Backtest mode (default: False)
        start: str
            Backtest start date (YYYY-MM-DD [HH:MM:SS[.MS]). Default is None
        end: str
            Backtest end date (YYYY-MM-DD [HH:MM:SS[.MS]). Default is None
        data : str
            Path to the directory with QTPyLib-compatible CSV files (Backtest)
        output: str
            Path to save the recorded data (default: None)
        zmqport : str
            ZeroMQ Port to use (default: 12345)
        zmqtopic : str
            ZeroMQ string to use (default: _qtpylib_BLOTTERNAME_)
        appurl : str
                URL of app vizualisation
    """

    __metaclass__ = ABCMeta

    def __init__(self, instruments=None, resolution="1H",
                 tick_window=1, bar_window=150, preload=None,
                 blotter=None, sms=None, slack=False, channel='random', log=None,
                 backtest=False, start=None, end=None, data=None, output=None,
                 ibclient=998, ibport=4001, ibserver=None,freshstart=0,
                 zmqport=None, zmqtopic=None,market=None,appurl='',
                 **kwargs):

        # detect algo name
        self.name = str(self.__class__).split('.')[-1].split("'")[0]
        name = tools.read_single_argv("--name")
        if name is not None:
            self.name = name
        print("name is : %s"%self.name )

        self.market = tools.read_single_argv("--market")
        if market is not None:
            self.market = market

        if zmqtopic is None:
            zmqtopic = "_qtpylib_" + str(self.market.lower()) + "_"
        print("zmqtopic is : %s"%zmqtopic)

        # initilize algo logger
        self.log_algo = logging.getLogger(__name__)

        # initilize strategy logger
        tools.createLogger(self.name, level=logging.INFO)
        self.log = logging.getLogger(self.name)

        # override args with any (non-default) command-line args
        self.args = {arg: val for arg, val in locals().items(
        ) if arg not in ('__class__', 'self', 'kwargs')}
        self.args.update(kwargs)
        self.args.update(self.load_cli_args())

        # -----------------------------------
        # assign algo params
        self.quotes = {}
        self.books = {}
        self.tick_count = 0
        self.tick_bar_count = 0
        self.bar_count = 0
        self.bar_hashes = {}

        self.tick_window = tick_window if tick_window > 0 else 1
        if "V" in resolution:
            self.tick_window = 1000
        self.bar_window = [bar_window if bar_window > 0 else 150]
        self.resolution = resolution.upper().replace("MIN", "T")
        self.preload = preload

        # -----------------------------------
        # backtest info
        self.backtest = self.args["backtest"]
        self.backtest_start = self.args["start"]
        self.backtest_end = self.args["end"]
        self.backtest_csv = self.args["data"]

        # -----------------------------------
        self.sms_numbers = self.args["sms"]
        self.trade_log_dir = self.args["log"]
        self.blotter_name = self.args["blotter"]
        self.record_output = self.args["output"]

        self.ibConn = ezibpy.ezIBpy()
        # -----------------------------------
        self.dbcurr = None
        self.dbconn = None

        self.duplicate_run = False
        self.args_cache_file = "%s/%s.qtpylib" % (
            tempfile.gettempdir(), self.name)
        if os.path.exists(self.args_cache_file):
            self.cahced_args = self._read_cached_args()

        # -----------------------------------
        # initiate broker/order manager
        print(self.args)
        super().__init__(instruments, **{
            arg: val for arg, val in self.args.items() if arg in (
                'ibport', 'ibclient', 'ibserver')})


        print("symbols are : %s"%self.symbols  )
        # -----------------------------------
        # tunnel threshold
        self.tunnel_threshold = {}
        for sym in self.symbols:
            self.tunnel_threshold[sym] = {}
        # -----------------------------------
        # signal collector

        self.signals = {}
        for sym in self.symbols:
            self.signals[sym] = pd.DataFrame()

        # -----------------------------------
        # initilize output file
        self.record_ts = None
        if self.record_output:
            self.datastore = tools.DataStore(self.args["output"])


        # ---------------------------------------
        # be aware of thread count
        self.threads = asynctools.multitasking.getPool(__name__)['threads']
        print("Number of threads :")
        print(self.threads)

        print('App URL : %s'%self.args['appurl'])
        print(self.blotter_args)


        self.symbol_ids = {symbol : get_symbol_id(symbol, self.dbconn, self.dbcurr) for symbol in self.symbols}

        # ---------------------------------------
        # Slack managment
        self.slack = self.args['slack']
        if self.slack :
            if 'channel' in self.args :
                self.channel = self.args['channel']
            else:
                self.channel = 'random'
                print("Post to channel %s"%self.channel)
            slack_api.join_channel(self.channel)
            slack_api.send_text("Run %s"%self.name, self.channel)

    # ---------------------------------------
    def load_cli_args(self):
        """
        Parse command line arguments and return only the non-default ones

        :Retruns: dict
            a dict of any non-default args passed on the command-line.
        """
        parser = argparse.ArgumentParser(
            description='QTPyLib Algo',
            formatter_class=argparse.ArgumentDefaultsHelpFormatter)

        parser.add_argument('--sms', default=self.args["sms"],
                            help='Numbers to text orders', nargs='+')
        parser.add_argument('--slack', default=self.args["slack"],action='store_true',
                            help='Send to slack')
        parser.add_argument('--channel', default=self.args["channel"],
                                help='Channel name', required=False)
        parser.add_argument('--log', default=self.args["log"],
                            help='Path to store trade data')
        parser.add_argument('--start', default=self.args["start"],
                            help='Backtest start date')
        parser.add_argument('--end', default=self.args["end"],
                            help='Backtest end date')
        parser.add_argument('--data', default=self.args["data"],
                            help='Path to backtester CSV files')
        parser.add_argument('--output', default=self.args["output"],
                            help='Path to save the recorded data')
        parser.add_argument('--blotter',
                            help='Log trades to this Blotter\'s MySQL')
        parser.add_argument('--ibport', default=self.args["ibport"],
                            help='IB TWS/GW Port', type=int)
        parser.add_argument('--ibclient', default=self.args["ibclient"],
                            help='IB TWS/GW Client ID', type=int)
        parser.add_argument('--ibserver', default=self.args["ibserver"],
                            help='IB TWS/GW Server hostname')
        parser.add_argument('--zmqport', default=self.args['zmqport'],
                                help='ZeroMQ Port to use', required=False)
        parser.add_argument('--freshstart', default=self.args["freshstart"],
                    help='Try to load previous state of model or recompute it at starting')
        parser.add_argument('--appurl', default='',
                help='URL of viz app (http://ip:port)')

        # only return non-default cmd line args
        # (meaning only those actually given)
        cmd_args, _ = parser.parse_known_args()
        args = {arg: val for arg, val in vars(
            cmd_args).items() if val != parser.get_default(arg)}
        return args

    # ---------------------------------------
    def initiate_socket(self):

        self.context = zmq.Context(zmq.REP)
        self.socket = self.context.socket(zmq.PUB)
        print("PUB to port %s"%self.args['zmqport'])
        self.socket.bind("tcp://*:" + str(self.args['zmqport']))

    # ---------------------------------------

    def get_history(self, symbol, granularity, window):
        req = """SELECT datetime, open, high, close, low, volume, symbol_id FROM bars_%s WHERE symbol_id=%s ORDER BY datetime DESC LIMIT %s"""

        if self.threads > 0:
            dbconn = self.get_mysql_connection()
        else:
            dbconn = self.dbconn

        if symbol not in self.symbol_ids:
            print('Contrat %s not in self.symbol_ids'%symbol)
            self.tunnel_threshold[symbol] = {}
            return

        bars = pd.read_sql(req%(granularity, self.symbol_ids[symbol], window), dbconn)

        bars.sort_values('datetime',inplace=True)

        if self.threads > 0:
            dbconn.close()

        return bars

    def fill_db(self):


        if self.ibserver:
            self.blotter.ibConn = self.ibConn
            # call the back fill
            print("++++++++ START OF BACKFILL ++++++++")
            #self.preload = ['21W','21D']#,'150H','1T']
            for (_,instrument) in self.instruments.items():
                contract = self.ibConn.createContract(instrument)
                print('***** Contract %s '% str(instrument))
                for preload in self.preload:
                    # Data check
                    start = tools.backdate(preload)
                    end =  None
                    print("Start date is :%s"%start)
                    print("End date is :%s"%end)
                    temp = re.compile("([0-9]+)([a-zA-Z]+)")
                    res = temp.match(preload).groups()
                    print(res[0], res[1])
                    ib_dic =  dict(W='week',D='day',H='hour',T="min")
                    granularity = ib_dic[res[1]]
                    window = res[0]
                    #bars = self.get_history(instrument[0], granularity, 2*window)
                    #bars = bars.set_index('datetime')
                    self.blotter.backfill(data=pd.DataFrame(),
                                          resolution=preload,
                                          start=start, end=end, contract = [contract])
                    time.sleep(10)

            print("++++++++ END OF BACKFILL ++++++++")
            self.blotter.ibConn = None


    def run(self):
        """Starts the algo

        Connects to the Blotter, processes market data and passes
        tick data to the ``on_tick`` function and bar data to the
        ``on_bar`` methods.
        """
        print('RUN')
        #self._check_unique_model()
        self.initiate_socket()
        # add instruments to blotter in case they do not exist
        #self.blotter.register(self.instruments)
        self.symbol_ids = {symbol : get_symbol_id(symbol, self.dbconn, self.dbcurr) for symbol in self.symbols}

        # initiate strategy
        self.on_start()
        print('On start finished')


        # listen for RT data
        #self._bar_handler({'cron':True, 'kind' : 'BAR', 'symbol':  ['ALXN','ALGN','AMGN']})
        """
        for symbol in ['FFP','RMS'] :
            self._bar_handler({"symbol":symbol, "type" : "BAR", 'timestamp':"2020-01-13 15:00:00"})
        """

        self.zmqport_list = range(int(self.blotter.args['zmqport']),int(self.args['zmqport']))
        print(self.zmqport_list)
        self.blotter.stream(
            symbols=self.symbols,
            tick_handler=self._tick_handler,
            bar_handler=self._bar_handler,
            tunnel_handler=self._tunnel_handler,
            overshoot_handler = self._overshoot_handler,
            cron_handler = self._cron_handler,
            contract_restriction=True,
            zmqport_list = self.zmqport_list
        )

    @asynctools.multitasking.task
    def _tick_handler(self, tick, stale_tick=False):
        self.on_tick(tick)

    @asynctools.multitasking.task
    def _cron_handler(self, data):
        self.on_cron(data)

    @asynctools.multitasking.task
    def _bar_handler(self, data):
        self._base_bar_handler(data)

    @asynctools.multitasking.task
    def _tunnel_handler(self, data):
        if data['type'] == "H":
            self.on_tunnel(data)
        elif data['type'] == "B":
            self.on_tunnel_out(data)

    @asynctools.multitasking.task
    def _overshoot_handler(self, data):
        self.on_overshoot(data)

    # ---------------------------------------
    @abstractmethod
    def on_overshoot(self):
        raise NotImplementedError("Should implement on_overshoot()")
        pass
    # ---------------------------------------
    @abstractmethod
    def on_tunnel(self):
        raise NotImplementedError("Should implement on_tunnel()")
        pass
    # ---------------------------------------
    @abstractmethod
    def on_tunnel_out(self):
        raise NotImplementedError("Should implement on_tunnel_out()")
        pass
    # ---------------------------------------
    def on_cron(self, data):
        # Check if all listening Zmq adress are sending cron
        pass
    # --------------------------------------

    def _base_bar_handler(self, data):
        """ non threaded bar handler (called by threaded _bar_handler) """
        # bar symbol
        if (data['granularity'] != 'hour') or ('cron' in data) :
            return


        print("Received at %s"%datetime.now())
        last_bar_datetime =  datetime.strptime(data['timestamp'],
            "%Y-%m-%d %H:%M:%S")
        symbol = data['symbol']
        #contract_open = ",".join([str(self.symbol_ids[contrat]) for contrat in contract_open])

        bars = self.get_history(symbol, 'hour', 150)
        if (bars is not None) and (not bars.empty):
            self.on_bar(symbol, bars, last_bar_datetime)

    # ---------------------------------------
    @abstractmethod
    def on_start(self):
        """
        Invoked once when algo starts. Used for when the strategy
        needs to initialize parameters upon starting.

        """
        raise NotImplementedError("Should implement on_start()")
        pass

    # ---------------------------------------
    @abstractmethod
    def on_quote(self, instrument):
        """
        Invoked on every quote captured for the selected instrument.
        This is where you'll write your strategy logic for quote events.

        :Parameters:

            symbol : string
                `Instruments Object <#instrument-api>`_

        """
        # raise NotImplementedError("Should implement on_quote()")
        pass

    # ---------------------------------------
    @abstractmethod
    def on_tick(self, instrument):
        """
        Invoked on every tick captured for the selected instrument.
        This is where you'll write your strategy logic for tick events.

        :Parameters:

            symbol : string
                `Instruments Object <#instrument-api>`_

        """
        # raise NotImplementedError("Should implement on_tick()")
        pass

    # ---------------------------------------
    @abstractmethod
    def on_bar(self, instrument):
        """
        Invoked on every tick captured for the selected instrument.
        This is where you'll write your strategy logic for bar events.

        :Parameters:

            instrument : object
                `Instruments Object <#instrument-api>`_

        """
        # raise NotImplementedError("Should implement on_bar()")
        pass

    # ---------------------------------------
    def record(self, *args, **kwargs):
        """Records data for later analysis.
        Values will be logged to the file specified via
        ``--output [file]`` (along with bar data) as
        csv/pickle/h5 file.

        Call from within your strategy:
        ``self.record(key=value)``

        :Parameters:
            ** kwargs : mixed
                The names and values to record

        """
        if self.record_output:
            try:
                self.datastore.record(self.record_ts, *args, **kwargs)
            except Exception as e:
                pass

    # ---------------------------------------
    def sms(self, text):
        """Sends an SMS message.
        Relies on properly setting up an SMS provider (refer to the
        SMS section of the documentation for more information about this)

        Call from within your strategy:
        ``self.sms("message text")``

        :Parameters:
            text : string
                The body of the SMS message to send

        """
        logging.info("SMS: %s", str(text))
        sms.send_text(self.name + ': ' + str(text), self.sms_numbers)


    # ---------------------------------------
    @staticmethod
    def _caller(caller):
        stack = [x[3] for x in inspect.stack()][1:-1]
        return caller in stack

    # ---------------------------------------
    @asynctools.multitasking.task
    def _book_handler(self, book):
        symbol = book['symbol']
        del book['symbol']
        del book['kind']

        self.books[symbol] = book
        self.on_orderbook(self.get_instrument(symbol))

    # ---------------------------------------
    @asynctools.multitasking.task
    def _quote_handler(self, quote):
        del quote['kind']
        self.quotes[quote['symbol']] = quote
        self.on_quote(self.get_instrument(quote))

    # ---------------------------------------
    @staticmethod
    def _get_window_per_symbol(df, window):
        # truncate tick window per symbol
        dfs = []
        for sym in list(df["symbol"].unique()):
            dfs.append(df[df['symbol'] == sym][-window:])
        return pd.concat(dfs, sort=True).sort_index()



    # ---------------------------------------
    def _update_window(self, df, data, window=None, resolution=None):
        if df is None:
            df = data
        else:
            df = df.append(data, sort=True)

        # resample
        if resolution:
            tz = str(df.index.tz)
            # try:
            #     tz = str(df.index.tz)
            # except Exception as e:
            #     tz = None
            df = tools.resample(df, resolution=resolution, tz=tz)

        else:
            # remove duplicates rows
            # (handled by resample if resolution is provided)
            df.loc[:, '_idx_'] = df.index
            df.drop_duplicates(
                subset=['_idx_', 'symbol', 'symbol_group', 'asset_class'],
                keep='last', inplace=True)
            df.drop('_idx_', axis=1, inplace=True)

        # return
        if window is None:
            return df

        # return df[-window:]
        return self._get_window_per_symbol(df, window)

    # ---------------------------------------
    # signal logging methods
    # ---------------------------------------
    def _add_signal_history(self, df, symbol):
        """ Initilize signal history """
        if symbol not in self.signals.keys() or len(self.signals[symbol]) == 0:
            self.signals[symbol] = [nan] * len(df.index)
        else:
            self.signals[symbol].append(nan)

        self.signals[symbol] = self.signals[symbol][-len(df.index):]
        signal_count = len(self.signals[symbol])
        df.loc[-signal_count:, 'signal'] = self.signals[symbol][-signal_count:]

        return df

    def _log_signal(self, symbol, signal):
        """ Log signal

        :Parameters:
            symbol : string
                instruments symbol
            signal : integer
                signal identifier (1, 0, -1)

        """
        self.signals[symbol][-1] = signal


    # ---------------------------------------
    # UTILITY FUNCTIONS
    # ---------------------------------------
    def get_instrument(self, symbol):
        """
        A string subclass that provides easy access to misc
        symbol-related methods and information using shorthand.
        Refer to the `Instruments API <#instrument-api>`_
        for available methods and properties

        Call from within your strategy:
        ``instrument = self.get_instrument("SYMBOL")``

        :Parameters:
            symbol : string
                instrument symbol

        """
        instrument = Instrument(self.get_symbol(symbol))
        instrument._set_parent(self)
        instrument._set_windows(ticks=self.tick_window, bars=self.bar_window)

        return instrument

    # ---------------------------------------
    @staticmethod
    def get_symbol(symbol):
        if not isinstance(symbol, str):
            if isinstance(symbol, dict):
                symbol = symbol['symbol']
            elif isinstance(symbol, pd.DataFrame):
                symbol = symbol[:1]['symbol'].values[0]

        return symbol

    def __getstate__(self):
        """ This is called before pickling. """
        return {}

    def __setstate__(self, state):
        """ This is called while unpickling. """
        self.__dict__.update(state)


    def get_mysql_connection(self):
        return pymysql.connect(
            host=str(self.blotter_args['dbhost']),
            port=int(self.blotter_args['dbport']),
            user=str(self.blotter_args['dbuser']),
            passwd=str(self.blotter_args['dbpass']),
            db=str(self.blotter_args['dbname'])
        )


    # -------------------------------------------
    @staticmethod
    def _model_file_running():
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
    @staticmethod
    def _model_file_running():
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
    def _check_unique_model(self):
        if os.path.exists(self.args_cache_file):
            # temp file found - check if really running
            # or if this file wasn't deleted due to crash
            if not self._model_file_running():
                # print("REMOVING OLD TEMP")
                self._remove_cached_args()
            else:
                self.duplicate_run = True
                self.log_blotter.error("Model is already running...")
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


    # ----------------------------------------------
    def broadcast(self, data, kind):

        string2send = "%s %s" % (
            self.args["zmqtopic"], json.dumps(data, cls=tools.MyEncoder))
        print(string2send)
        try:
            self.socket.send_string(string2send)
        except Exception as e:
            print('Broadcast error : ')
            print(e)
            pass

    # ---------------------------------------
    def post(self, text, channel=None):
        """Sends an slack message.
        Slack section of the documentation for more information about this)


        :Parameters:
            tunnel : text
                The body of the Slack message to send

        """
        if self.slack:
            logging.info("Slack: %s", str(text))
            slack_api.send_text(text, channel)
