"use strict";

// Registers test cases to be run against Test262
// To add a testcase to be tested against test262:
//   var test262tests = require('./helper-test262.js')'
//   test262tests.push(function testConstructorFunction(source, negativity) {});
//
// Tests are run in the order added to the array. If inter-module test ordering is required,
// ensure the later test module depends on the earlier one.
//
// Arguments to testConstructorFunction:
// - source: The raw test source code
// - negativity: The @negative test header content
// -

var fs = require('mz/fs');
var walk = require('klaw');
var filter = require('through2-filter');
fs.readlinkSync = require('readlink').sync; // a non-broken readlink...

var testConstructors = [];

function testNegativity(str) {
  var result = /@negative[ \t]*(\S*)?[ \t]*$/m.exec(str);
  if(result) {
    result = result[1] || true;
  } else {
    result = false;
  }
  return result;
}

before(function(done) {
  this.timeout(0); // Otherwise it fails on slow filesystems

  var test262path = fs.readlinkSync(__dirname + '/test262');
  var tests = [];

  walk(test262path)
  .pipe(filter.obj(file => file.stats.isFile() && file.path.endsWith(".js")))
  .on('readable', function() {
    var item;
    while((item = this.read())) { tests.push(item.path); }
  })
  .on('end', function() {
    describe("test262", function() {
      tests.forEach(item => {
        describe(item, function() {
          // Preseed test arguments with safe defaults
          var args = {
            source: "if // invalid syntax",
            negative: false
          };

          var source;
          var negative = '';

          before(function(doneFile) {
            fs.readFile(item).then(
              data => {
                args.source = data.toString();
                args.negative = testNegativity(args.source);
              }
            ).then(doneFile);
          });

          testConstructors.forEach(constructor => constructor(args));
        });
      });
    });

    done();
  });
});

module.exports = testConstructors;
