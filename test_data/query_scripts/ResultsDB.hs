{-# LANGUAGE ScopedTypeVariables #-}

module ResultsDB where

import Database.HDBC.Sqlite3(connectSqlite3)
import qualified Database.HDBC.Sqlite3 as Sqlite3 (Connection)
import Database.HDBC.PostgreSQL(connectPostgreSQL)
import qualified Database.HDBC.PostgreSQL as PostgreSQL (Connection)
import Database.HDBC(prepare,toSql,execute,fromSql,fetchRow,runRaw,IConnection)
import Data.Maybe(fromJust)
import System.Environment
import System.FilePath((</>),(<.>),takeDirectory)
import System.Directory
import Data.List(transpose)

strPASS :: String
strPASS = "PASS"
strFAIL :: String
strFAIL = "FAIL"
strABORT :: String
strABORT = "ABORT"

dbPathFromQueries :: IO FilePath
dbPathFromQueries = do
  dir <- getCurrentDirectory
  username <- getEnv "USER"
  return $ takeDirectory dir </> "test_results"<.>"db"

dbPathFromTrunk :: IO FilePath
dbPathFromTrunk = return $ "test_data" </> "test_results" <.> "db"

getConnectionFromQueries :: IO Sqlite3.Connection
getConnectionFromQueries = connectSqlite3 =<< dbPathFromQueries

getConnectionFromTrunk :: IO Sqlite3.Connection
getConnectionFromTrunk = connectSqlite3 =<< dbPathFromTrunk

getPostgresConnection :: IO PostgreSQL.Connection
getPostgresConnection = do
  con <- connectPostgreSQL =<< readFile ".pgconfig"
  runRaw con "SET SCHEMA 'jscert'"
  return con

stmtMakeGroup :: String
stmtMakeGroup = "INSERT INTO test_groups (description) VALUES (?)"

stmtMakeFailGroup :: String
stmtMakeFailGroup = "INSERT INTO fail_groups (description,reason) VALUES (?,?)"

stmtAddFileToGroup :: String
stmtAddFileToGroup = "INSERT INTO test_group_memberships (group_id,test_id) VALUES (?,?)"

stmtAddFileToFailGroup :: String
stmtAddFileToFailGroup = "INSERT INTO fail_group_memberships (group_id,test_id) VALUES (?,?)"

stmtGetLatestGroup :: String
stmtGetLatestGroup = "SELECT id from test_groups ORDER BY id DESC"

stmtGetLatestTestBatch :: String
stmtGetLatestTestBatch = "SELECT id from test_batch_runs ORDER BY id DESC"

stmtGetLatestFailGroup :: String
stmtGetLatestFailGroup = "SELECT id from fail_groups ORDER BY id DESC"


-- Returns the ID of the group we created
makeGroup :: IConnection connection => String -> connection -> IO Int
makeGroup desc con = do
      mkstmt <- prepare con stmtMakeGroup
      execute mkstmt [toSql desc]
      getstmt <- prepare con stmtGetLatestGroup
      execute getstmt []
      fmap (fromSql.head.fromJust) $ fetchRow getstmt

-- Returns the ID of the group we created
makeFailGroup :: IConnection connection => String -> String -> connection -> IO Int
makeFailGroup desc reason con = do
  mkFailGroup <- prepare con stmtMakeFailGroup
  execute mkFailGroup [toSql desc, toSql reason]
  getLatestFailG <- prepare con stmtGetLatestFailGroup
  execute getLatestFailG []
  fmap (fromSql.head.fromJust) $ fetchRow getLatestFailG

addFilesToSomeGroup :: IConnection connection => String -> Int -> [String] -> connection -> IO ()
addFilesToSomeGroup stmtstr gid tids con = do
  stmt <- prepare con stmtstr
  let stmtargs = transpose [replicate (length tids) (toSql gid) , map toSql tids]
  mapM_ (execute stmt) stmtargs

addFilesToGroup :: IConnection connection => Int -> [String] -> connection -> IO ()
addFilesToGroup = addFilesToSomeGroup stmtAddFileToGroup

addFilesToFailGroup :: IConnection connection => Int -> [String] -> connection -> IO ()
addFilesToFailGroup = addFilesToSomeGroup stmtAddFileToFailGroup
