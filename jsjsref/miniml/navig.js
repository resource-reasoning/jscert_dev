
tracer_items = datalog;
var h = null

var tracer_length = tracer_items.length;
var tracer_pos = 0; 

$("#navigation_total").html(tracer_length);


function stepTo(step) {
  tracer_pos = step;
  updateSelection();
}

$("#navigation_step").change(function(e) {
  var n = + $("#navigation_step").val();
  n = Math.max(0, Math.min(tracer_length, n));
  stepTo(n);
});

$("#button_run").click(function() {
 $("#run_output").html("Run successful !");
 var timeoutID = window.setTimeout(function() { $("#run_output").html(""); }, 1000);
});

$("#button_reset").click(function() {
 stepTo(0);
});

$("#button_prev").click(function() {
 stepTo(Math.max(0, tracer_pos-1));
});

$("#button_next").click(function() {
 stepTo(Math.min(tracer_length-1, tracer_pos+1));
});

$("#button_reach").click(function() {
 $("#reach_output").html("Not found");
 var timeoutID = window.setTimeout(function() { $("#reach_output").html(""); }, 1000);
});

// Assumes tracer_files to be an array of objects with two field:
// - file, containing the name of the file,
// - contents, a string containing its source code

// Assumes tracer_items to be an array with items, e.g.:
// { type: 'enter', file: 'foo.ml', start_line: 4, start_col: 0, end_line: 5, end_col: 10 },
// { type: 'exit', file: 'foo.ml', start_line: 4, start_col: 0, end_line: 5, end_col: 10 },
// { type: 'other_event', file: 'foo.ml', start_line: 4, start_col: 0, end_line: 5, end_col: 10 },

function tracer_valid_pos(i) {
  return (i >= 0 && i < tracer_length);
}

// dir is -1 or +1
function shared_step(dir) { 
  var i = tracer_pos;
  i += dir; 
  if (! tracer_valid_pos(i)) 
     return; // not found, we don’t update the tracer position.
  tracer_pos = i;
}

// dir is -1 or +1,
// target (= target depth) is 0 for (next/prev) or -1 (finish)
function shared_next(dir, target) { 
  var i = tracer_pos;
  var depth = 0;
  var ty = tracer_items[i].type;
  if (dir === +1 && ty === 'exit') {
     depth = 1;
  } else if (dir === -1 && ty === 'enter') {
     depth = -1;
  } 
  while (true) {
     if (! tracer_valid_pos(i)) {
        tracer_pos = i - dir; // just before out of range
        return; // not found
     }
     if (i !== tracer_pos && depth === target) {
        tracer_pos = i;
        return;
     }
     var ty = tracer_items[i].type;
     if (ty === 'enter') {
        depth++;
     } else if (ty === 'exit') {
        depth--;
     }
     i += dir; 
  }
}

function restart() { tracer_pos = 0; }
function step() { shared_step(+1); }
function backstep() { shared_step(-1); }
function next() { shared_next(+1, 0); }
function previous() { shared_next(-1, 0); }
function finish() { shared_next(+1, -1); } 

var curfile = '';

var docs = {};
for (var i = 0; i < tracer_files.length; i++) {
  var file = tracer_files[i].file;
  var txt = tracer_files[i].contents;
  docs[file] = CodeMirror.Doc(txt, 'js');
}

var editor = null;

function viewFile(file) {
  if (curfile !== file) {
     curfile = file;
     editor.swapDoc(docs[curfile]);
     editor.focus();
     updateFileList();
  }
}

function updateFileList() {
  var s = '';
  for (var i = 0; i < tracer_files.length; i++) {
     var file = tracer_files[i].file;
     s += "<span class=\"file_item" + ((curfile == file) ? '_current' : '') + "\" onclick=\"viewFile('" + file + "')\">" + file + "</span> ";
  }
  $('#file_list').html(s);
}

function updateSelection() {
  var item = tracer_items[tracer_pos];
  h = jsheap_of_heap(item.heap); // export for client
  viewFile(item.file);
  //console.log("pos: " + tracer_pos);
  var color = (item.type === 'enter') ? '#F3F781' : '#CCCCCC';
  //console.log("color " + color);
  $('.CodeMirror-selected').css({ background: color });
  $('.CodeMirror-focused .CodeMirror-selected').css({ background: color });
  if (item.line === undefined)
    alert("missing line in log event");
  $("#infos").html("type = " + item.type);
  $("#navigation_step").val(tracer_pos);
  console.log(item);
  var anchor = {line: item.start_line-1 , ch: item.start_col };
  var head = {line: item.end_line-1, ch: item.end_col };
  editor.setSelection(anchor, head);
  updateFileList();
}

editor = CodeMirror.fromTextArea(document.getElementById('interpreter_code'), {
  mode: 'js',
  lineNumbers: true,
  lineWrapping: true,
  readOnly: true,
  extraKeys: {
     'R': function(cm) { restart(); updateSelection(); },
     'S': function(cm) { step(); updateSelection(); },
     'B': function(cm) { backstep(); updateSelection(); },
     'N': function(cm) { next(); updateSelection(); },
     'P': function(cm) { previous(); updateSelection(); },
     'F': function(cm) { finish(); updateSelection(); },
  },
});
editor.setSize(600,300);

editor.on('dblclick', function() {
  var line = editor.getCursor().line;
  var txt = editor.getLine(line);
  var prefix = "#sec-";
  var pos_start = txt.indexOf(prefix);
  if (pos_start === -1)
     return;
  var pos_end = txt.indexOf("*", pos_start);
  if (pos_end === -1)
     return;
  var sec = txt.substring(pos_start, pos_end);
  var url = "http://www.ecma-international.org/ecma-262/5.1/" + sec;
  window.open(url, '_blank');
});

editor.focus();
updateSelection(editor);



/* demo
var j = jsheap_of_heap(heap);

for (var k = 0; k < datalog.length; k++) {
var item = datalog[k];
var jsheap = jsheap_of_heap(item.heap);
item.heap = jsheap;
item.env = jsenv_of_env(jsheap, item.env);
if (item.ctx !== undefined) {
item.ctx = jsenv_of_env(jsheap, item.ctx);
}
}
*/
