const smt2_conf = {
  autoClosingPairs: [
      { open: '(', close: ')' }
  ]
};

/* SMT2 language definition (borrowed from monaco editor languages) */
const smt2_lang = {

  // Set defaultToken to invalid to see what you do not tokenize yet
  // defaultToken: 'invalid',

  keywords: [
    'define-fun', 'define-const', 'assert', 'push', 'pop', 'assert', 'check-sat',
    'declare-const', 'declare-fun', 'get-model', 'get-value', 'declare-sort',
    'declare-datatypes', 'reset', 'eval', 'set-logic', 'help', 'get-assignment',
    'exit', 'get-proof', 'get-unsat-core', 'echo', 'let', 'forall', 'exists',
    'define-sort', 'set-option', 'get-option', 'set-info', 'check-sat-using', 'apply', 'simplify',
    'display', 'as', '!', 'get-info', 'declare-map', 'declare-rel', 'declare-var', 'rule',
    'query', 'get-user-tactics'
  ],

 operators: [
    '=', '&gt;', '&lt;', '&lt;=', '&gt;=', '=&gt;', '+', '-', '*', '/',
  ],

  builtins: [
    'mod', 'div', 'rem', '^', 'to_real', 'and', 'or', 'not', 'distinct',
    'to_int', 'is_int', '~', 'xor', 'if', 'ite', 'true', 'false', 'root-obj',
    'sat', 'unsat', 'const', 'map', 'store', 'select', 'sat', 'unsat',
    'bit1', 'bit0', 'bvneg', 'bvadd', 'bvsub', 'bvmul', 'bvsdiv', 'bvudiv', 'bvsrem',
    'bvurem', 'bvsmod',  'bvule', 'bvsle', 'bvuge', 'bvsge', 'bvult',
    'bvslt', 'bvugt', 'bvsgt', 'bvand', 'bvor', 'bvnot', 'bvxor', 'bvnand',
    'bvnor', 'bvxnor', 'concat', 'sign_extend', 'zero_extend', 'extract',
    'repeat', 'bvredor', 'bvredand', 'bvcomp', 'bvshl', 'bvlshr', 'bvashr',
    'rotate_left', 'rotate_right', 'get-assertions'
  ],

  brackets: [
    ['(',')','delimiter.parenthesis'],
    ['{','}','delimiter.curly'],
    ['[',']','delimiter.square']
  ],

  // we include these common regular expressions
  symbols:  /[=&gt;&lt;~&amp;|+\-*\/%@#]+/,

  // C# style strings
  escapes: /\\(?:[abfnrtv\\"']|x[0-9A-Fa-f]{1,4}|u[0-9A-Fa-f]{4}|U[0-9A-Fa-f]{8})/,

  // The main tokenizer for our languages
  tokenizer: {
    root: [
      // identifiers and keywords
      [/[a-z_][\w\-\.']*/, { cases: { '@builtins': 'predefined.identifier',
                                      '@keywords': 'keyword',
                                      '@default': 'identifier' } }],
      [/[A-Z][\w\-\.']*/, 'type.identifier' ],
      [/[:][\w\-\.']*/, 'string.identifier' ],
      [/[$?][\w\-\.']*/, 'constructor.identifier' ],

      // whitespace
      { include: '@whitespace' },

      // delimiters and operators
      [/[()\[\]]/, '@brackets'],
      [/@symbols/, { cases: { '@operators': 'predefined.operator',
                              '@default'  : 'operator' } } ],


      // numbers
      [/\d*\.\d+([eE][\-+]?\d+)?/, 'number.float'],
      [/0[xX][0-9a-fA-F]+/, 'number.hex'],
      [/#[xX][0-9a-fA-F]+/, 'number.hex'],
      [/#b[0-1]+/, 'number.binary'],
      [/\d+/, 'number'],

      // delimiter: after number because of .\d floats
      [/[,.]/, 'delimiter'],

      // strings
      [/"([^"\\]|\\.)*$/, 'string.invalid' ],  // non-teminated string
      [/"/,  { token: 'string.quote', bracket: '@open', next: '@string' } ],

      // user values
      [/\{/, { token: 'string.curly', bracket: '@open', next: '@uservalue' } ],
    ],

    uservalue: [
      [/[^\\\}]+/, 'string' ],
      [/\}/,       { token: 'string.curly', bracket: '@close', next: '@pop' } ],
      [/\\\}/,     'string.escape'],
      [/./,        'string']  // recover
    ],

    string: [
      [/[^\\"]+/,  'string'],
      [/@escapes/, 'string.escape'],
      [/\\./,      'string.escape.invalid'],
      [/"/,        { token: 'string.quote', bracket: '@close', next: '@pop' } ]
    ],

    whitespace: [
      [/[ \t\r\n]+/, 'white'],
      [/;.*$/,    'comment'],
    ],
  },
};

code = `% Click here and start typing.
`;

monaco.languages.register({ id: 'smt2' });
// Register a tokens provider for the language
monaco.languages.setLanguageConfiguration('smt2', smt2_conf);
monaco.languages.setMonarchTokensProvider('smt2', smt2_lang);

let apiUrl;
if (window.location.hostname == 'localhost' || window.location.hostname === '127.0.0.1') {
  apiUrl = 'http://localhost:8000/api/'; 
}
else{
  apiUrl = '/api/'; 
}


var editor = monaco.editor.create(document.getElementById('input'), {
  value: code,
  language: 'smt2',
  automaticLayout: true ,
  minimap: {
    enabled: false
}});

/* ---------------End of Editor Configuration--------------- */

loadResourceGuide('limboole-guide.html');
class StdinToStdoutProcessor {
  stdin() {
    if (this.input_str_pos < this.input_str.length) {
      let c = this.input_str.charCodeAt(this.input_str_pos);
      this.input_str_pos += 1;
      return c;
    } else {
      return null;
    }
  }
  stdout(code) {
    if (code === "\n".charCodeAt(0) && this.stdout_buf !== "") {
      this.print_line_stdout(this.stdout_buf + "\n");
      this.stdout_buf = "";
    } else {
      this.stdout_buf += String.fromCharCode(code);
    }
  }
  stderr(code) {
    if (code === "\n".charCodeAt(0) && this.stderr_buf !== "") {
      this.print_line_stderr(this.stderr_buf + "\n");
      this.stderr_buf = "";
    } else {
      this.stderr_buf += String.fromCharCode(code);
    }
  }

  constructor(creatorFunc, resolve, reject) {
    this.input_str_pos = 0;
    this.input_str = "";
    this.ready = false;

    this.stdout_buf = "";
    this.stderr_buf = "";

    let options = {
      preRun: function (mod) {
        function stdin() {
          return window.input__();
        }

        function stdout(c) {
          window.stdout__(c);
        }

        function stderr(c) {
          window.stderr__(c);
        }

        mod.FS.init(stdin, stdout, stderr);
      },
    };

    var self = this;

    //console.debug("Creating Processor");
    createLimbooleModule(options).then(function (Module) {
      self.Module = Module;
      window.input__ = function () {
        return "";
      };
      window.stdout__ = function (_) {};
      window.stderr__ = function (_) {};

      //console.debug("Initial Processor Startup");
      Module.callMain();
      //console.debug("Initialized Processor");
      self.limboole = Module.cwrap("limboole_extended", "number", [
        "number",
        "array",
        "number",
        "string",
        "number",
      ]);
      resolve();
      self.ready = true;
    });
  }

  run(input, satcheck, stdout_writeln, stderr_writeln) {
    this.input_str = input;
    this.input_str_pos = 0;
    this.print_line_stdout = stdout_writeln;
    this.print_line_stderr = stderr_writeln;

    window.stdout__ = this.stdout.bind(this);
    window.stderr__ = this.stderr.bind(this);

    let status = this.limboole(1, [""], satcheck, input, input.length);
    
    save_to_db(satcheck, input);

    if (this.stdout_buf != "") {
      this.print_line_stdout(this.stdout_buf);
      this.stdout_buf = "";
    }
    if (this.stderr_buf != "") {
      this.print_line_stderr(this.stdout_buf);
      this.stderr_buf = "";
    }
  }
}

class ProcessorWrapper {
  constructor(processor, name, args) {
    this.processor = processor;
    this.name = name;
    this.args = args;
  }

  run(input, stdout, stderr) {
    if (!this.ready()) {
      alert(
        "Not yet ready for execution! Wait until Limboole has been downloaded and compiled!"
      );
      return;
    }
    this.processor.run(input, this.args, stdout, stderr);
  }

  ready() {
    return this.processor.ready;
  }
}


function run_limboole(wrapper) {
  window.input_textarea = editor.getModel().getValue();
  window.stdout_textarea = document.getElementById("stdout");
  window.stderr_textarea = document.getElementById("stderr");

  function writeln(element, line) {
    element.value += line;

    element.style.height = "auto";
    element.style.height = element.scrollHeight + "px";
  }

  window.stdout_textarea.value = "";
  window.stderr_textarea.value = "";

  wrapper.run.bind(wrapper)(
    editor.getModel().getValue(),
    function (line) {
      writeln(window.stdout_textarea, line);
    },
    function (line) {
      writeln(window.stderr_textarea, line);
    }
  );
  run_button_enable();
}

window.LimbooleLoadedPromise = new Promise(function (resolve, reject) {
  window.Processors = [
    new StdinToStdoutProcessor(createLimbooleModule, resolve, reject),
  ];
});

window.Wrappers = [
  new ProcessorWrapper(window.Processors[0], "Limboole Validity", 0),
  new ProcessorWrapper(window.Processors[0], "Limboole Satisfiability", 1),
  new ProcessorWrapper(window.Processors[0], "Limboole QBF Satisfiability", 2),
];

let selector = document.getElementById("select_wrapper");
for (let i = 0; i < window.Wrappers.length; ++i) {
  let proc = window.Wrappers[i];
  let o = document.createElement("option");
  o.appendChild(document.createTextNode(proc.name));
  o.value = i;
  selector.appendChild(o);
}
let o_smt = document.createElement("option");
o_smt.appendChild(document.createTextNode("SMT"));
o_smt.value = 3;
selector.appendChild(o_smt);
let o_xmv = document.createElement("option");
o_xmv.appendChild(document.createTextNode("NuXMV"));
o_xmv.value = 4;
selector.appendChild(o_xmv);

var z3_loaded = false;
document.getElementById("info").style.display = "none";

Module = {};
Module.onRuntimeInitialized = () => { console.log("z3 loaded"); z3_loaded = true; };

Module.print = (text) => { 
  const info = document.getElementById("info");
  info.innerText += text + "\n";
};

function run_z3(code) {
  const info = document.getElementById("info");
  editor.getModel().setValue(code);
  if (z3_loaded) {
    try {
      info.innerText = "";
      save_to_db(3,code);
      let res = Z3.solve(code);
      info.innerText += res;
    } catch (error) {
      console.error(error);
      //info.innerText += error;
    }
  } else {
    info.innerText = "Wait for Z3 to load and try again."
  }
  run_button_enable()
}

var link = document.getElementById('smv-copyright');
link.style.display = 'none';
function run_nuxmv(code) {
  const info = document.getElementById("info");
  editor.getModel().setValue(code);
  fetch(apiUrl+'run_nuxmv', {
    method: 'POST',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({code: code}),
  })
  .then(response => {
    if (response.status === 200) {
        return response.json();
    } else if(response.status === 413){
      alert("Code size is too large!");
      throw new Error('Request failed with status ' + response.status);
    } else if(response.status === 429){
      alert("Slow Down! You've already made a request recently.");
      throw new Error('Request failed with status ' + response.status);
    }
  })
  .then(data => {
    try {
      info.innerText = "";

      info.innerText += data.result;
      save_to_db(4,code);
    } catch (error) {
      console.error(error);
      //info.innerText += error;
    }
    run_button_enable();
  })
  .catch((error) => {
    console.error('Error:', error);
  });

  //run_button_enable()

}

window.run_ = function () {
  let selector = document.getElementById("select_wrapper");
  var std_out_element = document.getElementById("stdout");
  var std_err_element = document.getElementById("stderr");
  var info_element = document.getElementById("info");
  var header_error_element = document.getElementById("header_error");
  var run_button = document.getElementById("run-btn");

  run_button.innerHTML = '<span class="spinner-border spinner-border-sm" role="status" aria-hidden="true"></span> Running...';
  run_button.disabled = true;
  
  if(selector.value < 3) {
    info_element.style.display = "none";
    std_err_element.style.display = "block";
    std_out_element.style.display = "block";
    header_error_element.style.display = "block"; 

    let wr = window.Wrappers[selector.options.selectedIndex];
    run_limboole(wr);
  }
  else if(selector.value == 3) {
    std_err_element.style.display = "none";
    std_out_element.style.display = "none";
    header_error_element.style.display = "none";
    info_element.style.display = "block";

    run_z3(editor.getModel().getValue());
  }
  else if(selector.value == 4) {
    std_err_element.style.display = "none";
    std_out_element.style.display = "none";
    header_error_element.style.display = "none";
    info_element.style.display = "block";

    run_nuxmv(editor.getModel().getValue());
  }

};

function save_to_db(satcheck, code){
  fetch(apiUrl+'save', {
    method: 'POST',
    credentials: 'include',
    headers: {
      'Content-Type': 'application/json',
    },
    body: JSON.stringify({parent: window.location.hash.substring(1), check: satcheck, code: code}),
  })
  .then(response => {
    if (response.status === 200) {
        return response.json();
    } 
    else if(response.status === 413){
      alert("Code size is too large!");
      throw new Error('Request failed with status ' + response.status);
    } 
    else if(response.status === 429) {
      alert("Slow Down! You've already made a request recently.");
      throw new Error('Request failed with status ' + response.status);
    }
  })
  .then(data => {
    window.location.hash = data.permalink;
    var copyText = document.getElementById("permalink");
    copyText.select();
    copyText.value = window.location.href;

  })
  .catch((error) => {
    console.error('Error:', error);
  });
}


function load_in_editor() {
  const info = document.getElementById("info");
  if(window.location.hash != "" && window.location.hash != undefined && window.location.hash != null){
    let permalink = window.location.hash.substring(1);
    let code_content;
    fetch(apiUrl+permalink)
    .then(response => {
      if (response.status === 404) {
        alert("Permalink not found!");
      }
      else if (!response.ok) {
        throw new Error('Network response was not ok');
      }
      return response.json();
    })
    .then(data => {
      code_content = data.code;
      editor.getModel().setValue(code_content);
      let v = permalink.charAt(0);
      selector.value = v;
      info.innerText = ""; 
      //Execute the code if limboole or z3
      // if(v < 3) {
      //   window.LimbooleLoadedPromise.then(function () {
      //     window.run_();
      //   });
      // }
    })
    .catch((error) => {
      console.error('Error:', error);
    }); 
  }
}

function run_button_enable() {
  var run_button = document.getElementById("run-btn");

  run_button.disabled = false;
  run_button.innerHTML = 'Run';
}


// TODO: change the editor language configuration (after having nuXMV syntax/grammar)
function handleOptionChange(selectElement) {
  let selectedValue = selectElement.value;
  var link = document.getElementById('smv-copyright');
  if (selectedValue < 3) {
    let code_on_editor = editor.getModel().getValue();
    let updated_code = code_on_editor.replace(/(--|;)/g, '%');
    editor.getModel().setValue(updated_code);
    loadResourceGuide('limboole-guide.html');
  }
  if (selectedValue == 3) {
    let code_on_editor = editor.getModel().getValue();
    let updated_code = code_on_editor.replace(/(--|%)/g, ';');
    editor.getModel().setValue(updated_code);
    loadResourceGuide('smt-guide.html');
  }
  if (selectedValue == 4) {
    link.style.display = 'inline';
    let code_on_editor = editor.getModel().getValue();
    let updated_code = code_on_editor.replace(/^[;%]/, '--');
    editor.getModel().setValue(updated_code);
    loadResourceGuide('smv-guide.html');
  }
  else {
    link.style.display = 'none';
}
  // alert("Selected value: " + selectedValue);
}

function copy_permalink(){
  var copyText = document.getElementById("permalink");
  copyText.select();
  copyText.setSelectionRange(0, 99999); /*For mobile devices*/
  navigator.clipboard.writeText(copyText.value);
}


function uploadFile() {

  var input = document.createElement('input');
  input.type = 'file';
  input.accept = '.txt, .smt2, smv'; // Optionally, you can restrict the file type

  input.onchange = function(e) {
      var file = e.target.files[0];
      var reader = new FileReader();

      reader.onload = function() {
        editor.getModel().setValue(reader.result);
      }

      reader.readAsText(file);
  }

  input.click();
}

function downloadFile() {
  let selector = document.getElementById("select_wrapper");
  const content = editor.getModel().getValue();

  let filename = "code.txt"
  if(selector.value < 3){
    filename = 'code.txt';
  }else if(selector.value == 3){
    filename = 'code.smt2';
  }else if(selector.value == 4){
    filename = 'code.smv';
  }

  const blob = new Blob([content], { type: 'text/plain'});
  const url = window.URL.createObjectURL(blob);

  const a = document.createElement('a');
  a.href = url;
  a.download = filename;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
}


function loadResourceGuide(filename) {

  var xhr = new XMLHttpRequest();
  xhr.onreadystatechange = function() {
      if (xhr.readyState === XMLHttpRequest.DONE) {
          if (xhr.status === 200) {
              document.getElementById("resource-guide-wrapper").innerHTML = xhr.responseText;
          }
      }
  };

  xhr.open("GET", "./static/html/"+filename, true);
  xhr.send();
}


load_in_editor()