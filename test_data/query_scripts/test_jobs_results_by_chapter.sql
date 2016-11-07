SELECT
  test_cases.chapter1,
  test_cases.chapter2,
  test_cases.chapter3,
  count(test_runs.result = 'PASS' OR NULL) AS "pass",
  count(test_runs.result = 'FAIL' OR NULL) AS "fail",
  count(test_runs.result = 'ABORT' OR NULL) AS "abort",
  count(test_runs.result = 'UNKNOWN' OR NULL) AS "unknown",
  count(*) AS "total"
  , count(test_runs.result = 'PASS' OR NULL)*100 / count(*) AS "% pass"
FROM
  jscert.test_batches,
  jscert.test_runs,
  jscert.test_cases
WHERE
  test_runs.batch_id = test_batches.id
  AND test_batches.job_id = 214
  AND test_cases.id = test_runs.test_id
GROUP BY
  test_cases.chapter1, test_cases.chapter2,
  test_cases.chapter3
ORDER BY
  test_cases.chapter1, test_cases.chapter2,
  test_cases.chapter3
;
