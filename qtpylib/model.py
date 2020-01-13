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
import inspect
import sys
import logging
import os
import ezibpy
import pymysql
from multiprocessing import Pool, cpu_count

from datetime import datetime
from abc import ABCMeta, abstractmethod

import pandas as pd
from numpy import nan

from qtpylib.broker import Broker
from qtpylib.workflow import validate_columns as validate_csv_columns
from qtpylib.blotter_5min import prepare_history
from qtpylib import (
    tools, sms, asynctools
)
from qtpylib.instrument import Instrument

from qtpylib.blotter_5min import (
    Blotter, load_blotter_args, get_symbol_id
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


class Model():
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

    """

    __metaclass__ = ABCMeta

    def __init__(self, instruments=None, resolution="5T",
                 tick_window=1, bar_window=100, preload=None,
                 blotter=None, sms=None, log=None,
                 backtest=False, start=None, end=None, data=None, output=None,
                 **kwargs):

        # detect algo name
        self.name = str(self.__class__).split('.')[-1].split("'")[0]

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
        self.bars = pd.DataFrame()
        self.ticks = pd.DataFrame()
        self.quotes = {}
        self.books = {}
        self.tick_count = 0
        self.tick_bar_count = 0
        self.bar_count = 0
        self.bar_hashes = {}

        self.tick_window = tick_window if tick_window > 0 else 1
        if "V" in resolution:
            self.tick_window = 1000
        self.bar_window = bar_window if bar_window > 0 else 100
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

        # -----------------------------------
        # load blotter settings
        self.blotter_args = load_blotter_args(
            self.blotter_name, logger=self.log_algo)

        print(self.blotter_args)
        self.blotter = Blotter(**self.blotter_args)

        # connect to mysql using blotter's settings
        if not self.blotter_args['dbskip']:
            self.dbconn = pymysql.connect(
                host=str(self.blotter_args['dbhost']),
                port=int(self.blotter_args['dbport']),
                user=str(self.blotter_args['dbuser']),
                passwd=str(self.blotter_args['dbpass']),
                db=str(self.blotter_args['dbname']),
                autocommit=True
            )
            self.dbcurr = self.dbconn.cursor()
        # create contracts
        instrument_tuples_dict = {}
        if not instruments:
            df = pd.read_csv(self.blotter_args['symbols'], header=0)
            instruments = [tuple(x) for x in df[['symbol', 'sec_type', 'exchange',
                                  'currency', 'expiry', 'strike', 'opt_type']].values]


        for instrument in instruments:
            try:
                if isinstance(instrument, ezibpy.utils.Contract):
                    instrument = self.ibConn.contract_to_tuple(instrument)
                else:
                    instrument = tools.create_ib_tuple(instrument)
                contractString = self.ibConn.contractString(instrument)
                instrument_tuples_dict[contractString] = instrument
                self.ibConn.createContract(instrument)
            except Exception as e:
                pass


        self.instruments = instrument_tuples_dict
        self.symbols = list(self.instruments.keys())
        print("symbols are : %s"%self.symbols  )
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


        # only return non-default cmd line args
        # (meaning only those actually given)
        cmd_args, _ = parser.parse_known_args()
        args = {arg: val for arg, val in vars(
            cmd_args).items() if val != parser.get_default(arg)}
        return args

    # ---------------------------------------
    def run(self):
        """Starts the algo

        Connects to the Blotter, processes market data and passes
        tick data to the ``on_tick`` function and bar data to the
        ``on_bar`` methods.
        """

        history = pd.DataFrame()
        # optimize pandas
        if not history.empty:
            history['symbol'] = history['symbol'].astype('category')
            history['symbol_group'] = history['symbol_group'].astype('category')
            history['asset_class'] = history['asset_class'].astype('category')


        # place history self.bars
        self.bars = history

        # add instruments to blotter in case they do not exist
        self.blotter.register(self.instruments)
        self.symbol_ids = {symbol : get_symbol_id(symbol, self.dbconn, self.dbcurr) for symbol in self.symbols}
        print("self.symbol_ids : ")
        print(self.symbol_ids)

        # initiate strategy
        self.on_start()
        # listen for RT data
        self._bar_handler({'cron':True, 'kind' : 'BAR', 'symbol':  ['ALXN','ALGN','AMGN']})

        """
        self.blotter.stream(
            symbols=self.symbols,
            tick_handler=self._tick_handler,
            bar_handler=self._bar_handler,
            contract_restriction=False
        )
        """

    @asynctools.multitasking.task
    def _tick_handler(self, tick, stale_tick=False):

        # tick symbol
        symbol = tick['symbol']
        print("symbol in _tick_handler ")
        print("Received at %s"%datetime.now())
    # ---------------------------------------
    def _bar_handler(self, data):
        """ non threaded bar handler (called by threaded _tick_handler) """
        # bar symbol
        print(self.model)
        if 'cron' in data and data['cron']:
            print("Received at %s"%datetime.now())
            print('Bra created at %s'%data[''])
            last_bar_datetime = data['timestamp']
            #contract_open = ",".join([str(self.symbol_ids[contrat]) for contrat in contract_open])

            bars_to_process = []

            for contrat in contract_open:
                req = """SELECT datetime, open, high, close, low, volume, symbol_id FROM bars_hour WHERE symbol_id=%s ORDER BY datetime DESC LIMIT %s"""
                bars = pd.read_sql(req%(self.symbol_ids[contrat], self.bar_window),self.dbconn)

                bars_to_process += [(contrat, bars)]

            pool = Pool(2) # from pathos, Poll for multiprocessing. multiprocessing cannot pickle inside function main

            dataset = pd.concat(pool.map(self.on_bar, bars_to_process),
                                    ignore_index=True, axis=0)

            print(dataset)
            # inference
            y_pred = self.model.predict(dataset)
            proba = self.model.predict_proba(dataset)[:,1]
            print(proba)
            pool.close()




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
    def get_history(self, symbols, start, end=None, resolution="1T", tz="UTC"):
        """Get historical market data.
        Connects to Blotter and gets historical data from storage

        :Parameters:
            symbols : list
                List of symbols to fetch history for
            start : datetime / string
                History time period start date
                datetime or YYYY-MM-DD[ HH:MM[:SS]] string)

        :Optional:
            end : datetime / string
                History time period end date
                (datetime or YYYY-MM-DD[ HH:MM[:SS]] string)
            resolution : string
                History resoluton (Pandas resample, defaults to 1T/1min)
            tz : string
                History timezone (defaults to UTC)

        :Returns:
            history : pd.DataFrame
                Pandas DataFrame object with historical data for all symbols
        """
        return self.blotter.history(symbols, start, end, resolution, tz)


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
