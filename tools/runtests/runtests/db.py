import os
import re
import sqlite3
try:
    import psycopg2
except ImportError:
    psycopg2 = None

from .resulthandler import TestResultHandler


class DBManager(TestResultHandler):
    conn = None
    cur = None
    wait_for_batch = False

    def __del__(self):
        self.disconnect()

    def connect(self):
        """Only implement for db backends with limited connection pools"""
        pass

    def disconnect(self):
        """Only implement for db backends with limited connection pools, or require explicit commit"""
        pass

    def insert_testcases(self, testcases):
        """Bulk inserts testcase data and commits"""
        tcds = map(lambda t: t.db_tc_dict(), testcases)
        self.insert_ignore_many("test_cases", tcds)

    def create_job_batches_runs(self, job):
        self.insert_object(job)
        for batch in job.batches:
            self.insert_object(batch)
            for test in batch.get_testcases():
                self.insert_object(test)
        self.conn.commit()

    def start_batch(self, batch):
        self.connect()
        self.update_object(batch)
        self.conn.commit()
        if self.wait_for_batch:
            self.disconnect()

    def start_test(self, testcase):
        pass

    def finish_test(self, testcase):
        if not self.wait_for_batch:
            self.update_object(testcase)
            self.conn.commit()

    def finish_batch(self, batch):
        self.connect()
        if self.wait_for_batch:
            self.update_objects(batch.get_finished_testcases())
        self.update_object(batch)
        self.conn.commit()
        self.disconnect()

    # Helper functions
    def insert_ignore_many(self, table, coll):
        # TODO: sqlalchemy implementation
        """Insert or ignore row with colliding ID and commits"""
        raise NotImplementedError

    def insert_object(self, obj):
        self.session.add(obj)

    def update_object(self, obj):
        pass

    def update_objects(self, objs):
        pass

    def load_batch_tests(self, job_id, batch_idx):
        # FIXME
        batch_id_sql = """SELECT id FROM test_batches WHERE job_id = %s ORDER BY
                          id LIMIT 1 OFFSET %s"""
        self.cur.execute(batch_id_sql, (job_id, batch_idx))
        (batch_id,) = self.cur.fetchone()

        tests_sql = "SELECT id, test_id FROM test_runs WHERE batch_id = %s"
        self.cur.execute(tests_sql, (batch_id,))
        return (batch_id, self.cur.fetchall())

    def import_schema(self):
        # Deprecate?
        pass

    @staticmethod
    def from_args(args):
        dbmanager = None
        if args.db:
            if args.db == "sqlite":
                if not args.dbpath:
                    args.dbpath = os.path.join(
                        JSCERT_ROOT_DIR, "test_data", "test_results.db")

                dbmanager = SQLiteDBManager(args.dbpath, args.db_init)

            elif args.db == "postgres":
                if not args.dbpath:
                    args.dbpath = os.path.join(JSCERT_ROOT_DIR, ".pgconfig")
                try:
                    with open(args.dbpath, "r") as f:
                        dbmanager = PostgresDBManager(
                            f.readline(), args.db_pg_schema)
                except IOError as e:
                    raise Exception(
                        "Could not open postgres configuration: %s" % e)

            if args.db_init:
                dbmanager.connect()
                dbmanager.import_schema()
                print("Database created successfully")
                exit(0)

            if args.executor is 'condor':
                dbmanager.wait_for_batch = True
            dbmanager.connect()

        return dbmanager

# SQLite update_ignore
#        sql = ("INSERT OR IGNORE INTO %s (%s) VALUES (%s)" %
# Postgres update_ignore
#        sql = ("INSERT INTO %s (%s) SELECT %s WHERE NOT EXISTS (SELECT 1 FROM %s WHERE id = %s)" %
#
#        self.cur.execute("LOCK TABLE %s IN SHARE ROW EXCLUSIVE MODE" % table)
#        self.cur.executemany(sql, coll)
#        self.conn.commit()

