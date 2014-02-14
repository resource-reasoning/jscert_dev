#!/bin/bash
condor_submit -append "+tests = {\"test1\",\"test2\"}" -append "queue 2" condor_tests.cmd
