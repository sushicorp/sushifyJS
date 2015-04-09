var jsp = require("../uglify-js.js").parser;
var pro = require("../uglify-js.js").uglify;
var Vue = require("vue");


new Vue({
    el: "#main",
    data: {
        jssrc : "",
        jsresult : "",
        errormessage: ""
    },
    methods: {
        compile: function(){
            try{
                var orig_code = this.jssrc;
                var ast = jsp.parse(orig_code); // parse code and get the initial AST
                ast = pro.ast_mangle(ast); // get a new AST with mangled names
                ast = pro.ast_squeeze(ast); // get an AST with compression optimizations
                this.jsresult = pro.gen_code(ast); // compressed code here
            }catch(e){
                this.errormessage = e;
            }
        }
    },
    ready: function(){
        this.compile();
    }
});