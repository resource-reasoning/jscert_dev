SELECT 
  new_runs.test_id
FROM 
  jscert.test_runs old_runs, 
  jscert.test_batches old_batch, 
  jscert.test_runs new_runs, 
  jscert.test_batches new_batch
WHERE 
  old_runs.batch_id = old_batch.id AND
  new_runs.batch_id = new_batch.id AND
  new_runs.test_id = old_runs.test_id AND
  old_batch.job_id = 185 AND
  new_batch.job_id = 189 AND
  new_runs.result != old_runs.result AND
  old_runs.result = 'PASS'
  ;
