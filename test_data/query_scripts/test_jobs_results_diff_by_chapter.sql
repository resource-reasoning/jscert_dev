SELECT
  old.chapter1, old.chapter2, old.chapter3, old.chapter4,
  (new.pass - old.pass) AS "pass_diff",
  (new.fail - old.fail) AS "fail_diff",
  (new.abort - old.abort) AS "abort_diff"
FROM
(SELECT
  test_cases.chapter1,
  test_cases.chapter2,
  test_cases.chapter3,
  test_cases.chapter4,
  count(test_runs.result = 'PASS' OR NULL) AS "pass",
  count(test_runs.result = 'FAIL' OR NULL) AS "fail",
  count(test_runs.result = 'ABORT' OR NULL) AS "abort",
  count(test_runs.result = 'UNKNOWN' OR NULL) AS "unknown",
  count(*) AS "total"
FROM
  jscert.test_batches,
  jscert.test_runs,
  jscert.test_cases
WHERE
  test_runs.batch_id = test_batches.id
  AND test_batches.job_id = 185
  AND test_cases.id = test_runs.test_id
GROUP BY
  test_cases.chapter1, test_cases.chapter2,
  test_cases.chapter3, test_cases.chapter4
) "old",
(SELECT
  test_cases.chapter1,
  test_cases.chapter2,
  test_cases.chapter3,
  test_cases.chapter4,
  count(test_runs.result = 'PASS' OR NULL) AS "pass",
  count(test_runs.result = 'FAIL' OR NULL) AS "fail",
  count(test_runs.result = 'ABORT' OR NULL) AS "abort",
  count(test_runs.result = 'UNKNOWN' OR NULL) AS "unknown",
  count(*) AS "total"
FROM
  jscert.test_batches,
  jscert.test_runs,
  jscert.test_cases
WHERE
  test_runs.batch_id = test_batches.id
  AND test_batches.job_id = 196
  AND test_cases.id = test_runs.test_id
GROUP BY
  test_cases.chapter1, test_cases.chapter2,
  test_cases.chapter3, test_cases.chapter4
) "new"
WHERE old.chapter1 = new.chapter1 and old.chapter2 = new.chapter2
and old.chapter3 = new.chapter3 and old.chapter4 = new.chapter4
ORDER BY old.chapter1, old.chapter2, old.chapter3, old.chapter4
;
