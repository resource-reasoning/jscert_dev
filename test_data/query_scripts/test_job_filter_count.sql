SELECT
  COALESCE(test_groups.description, 'TODO: Not yet classified') description,
  count(*)
FROM
  (jscert.test_runs LEFT OUTER JOIN jscert.test_group_memberships USING (test_id))
  LEFT OUTER JOIN jscert.test_groups ON test_group_memberships.group_id = test_groups.id
  JOIN jscert.test_batches ON test_runs.batch_id = test_batches.id
  JOIN jscert.test_cases ON test_id = test_cases.id
WHERE
      test_runs.result <> 'PASS'
  AND job_id = 227
  AND (group_id >= 34 OR group_id IS NULL)
--  AND chapter1 >= 8 AND chapter1 <= 14
  AND chapter1 = 15 AND chapter2 = 4
GROUP BY
  group_id, description
ORDER BY
  count desc, group_id
;
