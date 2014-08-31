var esprima = require('esprima');
var fs = require('fs');
var filename = process.argv[2];
var force_strict = process.argv[3];
fs.readFile(filename, "utf8", f);

function f(err, data) {
  var strict = (force_strict === "-force_strict");
  var out = JSON.stringify(esprima.parse(data, {range: true, force_strict: strict}), null, 4);
  var output = filename.substring(0, (filename.length - 3)) + ".json";
  fs.writeFile(output, out, [], null);
}
