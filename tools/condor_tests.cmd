universe        = vanilla

# This defines the path of the executable we want to run.
executable      = /bin/echo

# This specifies where data sent to STDOUT by the executable should be
# directed to.
#
# The Condor system can perform variable substitution in job specifications;
# the $(Process) string below will be replaced with the job's Process value.
# If we submit multiple jobs from this single specification (we do, as you 
# will see later) then the Process value will be incremented for each job.
# For example, if we submit 100 jobs, then each job will have a different 
# Process value, numbered in sequence from 0 to 99.
#
# If we were to instruct every job to redirect STDOUT to the same file, then
# data would be lost as each job would overwrite the same file in an 
# uncontrolled manner.  Thus, we direct STDOUT for each job to a uniquely 
# named file.
output          = testing.$(Process).out

# As above, but for STDERR.
error           = testing.$(Process).err

# Condor can write a time-ordered log of events related to this job-set
# to a file we specify.  This specifies where that file should be written.
log             = condor_testing.log

# Assing to a Condor scheduling group (optional)
+AccountingGroup = "jscert"

# Selects ProcId'th from the tests array
arguments  = $$([tests[ProcId]])

# tests array appended dynamically on submit by condor_tests.sh script
# +tests = { "test1", "test2", ... }

# Queue command appended dynamically on submit by condor_tests.sh script
# queue 100
