import unittest
import time
from datetime import datetime, timedelta
from runtests.util import Timer, SubclassSelectorMixin


class TestTimer(unittest.TestCase):
    def test_timer_sets_start_time(self):
        timer = Timer()
        timer.start_timer()
        self.assertIsInstance(timer.start_time, datetime)
        self.assertIsNone(timer.stop_time)

    def test_timer_sets_stop_time(self):
        timer = Timer()
        timer.start_timer()
        timer.stop_timer()
        self.assertIsInstance(timer.start_time, datetime)
        self.assertIsInstance(timer.stop_time, datetime)

    def test_timer_sets_duration(self):
        timer = Timer()
        timer.start_timer()
        time.sleep(0.1)
        timer.stop_timer()
        self.assertGreater(timer.duration, 0)

    def test_timer_get_delta(self):
        timer = Timer()
        timer.start_timer()
        time.sleep(0.1)
        timer.stop_timer()
        delta = timer.get_delta()
        self.assertIsInstance(delta, timedelta)

    def test_timer_delta_equals_duration(self):
        timer = Timer()
        timer.start_timer()
        time.sleep(0.1)
        timer.stop_timer()
        delta = timer.get_delta()
        self.assertEqual(delta.total_seconds(), timer.duration)

    def test_timer_stop_exception(self):
        timer = Timer()
        with self.assertRaises(Exception):
            timer.stop_timer()

    def test_timer_get_delta_exception(self):
        timer = Timer()
        with self.assertRaises(Exception):
            timer.get_delta()
