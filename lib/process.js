/***********************************************************************

  A JavaScript tokenizer / parser / beautifier / compressor.

  This version is suitable for Node.js.  With minimal changes (the
  exports stuff) it should work on any JS platform.

  This file implements some AST processors.  They work on data built
  by parse-js.

  Exported functions:

    - ast_mangle(ast, options) -- mangles the variable/function names
      in the AST.  Returns an AST.

    - ast_squeeze(ast) -- employs various optimizations to make the
      final generated code even smaller.  Returns an AST.

    - gen_code(ast, options) -- generates JS code from the AST.  Pass
      true (or an object, see the code for some options) as second
      argument to get "pretty" (indented) code.

  -------------------------------- (C) ---------------------------------

                           Author: Mihai Bazon
                         <mihai.bazon@gmail.com>
                       http://mihai.bazon.net/blog

  Distributed under the BSD license:

    Copyright 2010 (c) Mihai Bazon <mihai.bazon@gmail.com>

    Redistribution and use in source and binary forms, with or without
    modification, are permitted provided that the following conditions
    are met:

        * Redistributions of source code must retain the above
          copyright notice, this list of conditions and the following
          disclaimer.

        * Redistributions in binary form must reproduce the above
          copyright notice, this list of conditions and the following
          disclaimer in the documentation and/or other materials
          provided with the distribution.

    THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER “AS IS” AND ANY
    EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
    IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
    PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE
    LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY,
    OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
    PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
    PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
    THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR
    TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
    THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
    SUCH DAMAGE.

 ***********************************************************************/

var jsp = require("./parse-js"),
    curry = jsp.curry,
    slice = jsp.slice,
    member = jsp.member,
    is_identifier_char = jsp.is_identifier_char,
    PRECEDENCE = jsp.PRECEDENCE,
    OPERATORS = jsp.OPERATORS;

/* -----[ helper for AST traversal ]----- */

function ast_walker() {
    function _vardefs(defs) {
        return [ this[0], MAP(defs, function(def){
            var a = [ def[0] ];
            if (def.length > 1)
                a[1] = walk(def[1]);
            return a;
        }) ];
    };
    function _block(statements) {
        var out = [ this[0] ];
        if (statements != null)
            out.push(MAP(statements, walk));
        return out;
    };
    var walkers = {
        "string": function(str) {
            return [ this[0], str ];
        },
        "num": function(num) {
            return [ this[0], num ];
        },
        "name": function(name) {
            return [ this[0], name ];
        },
        "toplevel": function(statements) {
            return [ this[0], MAP(statements, walk) ];
        },
        "block": _block,
        "splice": _block,
        "var": _vardefs,
        "const": _vardefs,
        "try": function(t, c, f) {
            return [
                this[0],
                MAP(t, walk),
                c != null ? [ c[0], MAP(c[1], walk) ] : null,
                f != null ? MAP(f, walk) : null
            ];
        },
        "throw": function(expr) {
            return [ this[0], walk(expr) ];
        },
        "new": function(ctor, args) {
            return [ this[0], walk(ctor), MAP(args, walk) ];
        },
        "switch": function(expr, body) {
            return [ this[0], walk(expr), MAP(body, function(branch){
                return [ branch[0] ? walk(branch[0]) : null,
                         MAP(branch[1], walk) ];
            }) ];
        },
        "break": function(label) {
            return [ this[0], label ];
        },
        "continue": function(label) {
            return [ this[0], label ];
        },
        "conditional": function(cond, t, e) {
            return [ this[0], walk(cond), walk(t), walk(e) ];
        },
        "assign": function(op, lvalue, rvalue) {
            return [ this[0], op, walk(lvalue), walk(rvalue) ];
        },
        "dot": function(expr) {
            return [ this[0], walk(expr) ].concat(slice(arguments, 1));
        },
        "call": function(expr, args) {
            return [ this[0], walk(expr), MAP(args, walk) ];
        },
        "function": function(name, args, body) {
            return [ this[0], name, args.slice(), MAP(body, walk) ];
        },
        "debugger": function() {
            return [ this[0] ];
        },
        "defun": function(name, args, body) {
            return [ this[0], name, args.slice(), MAP(body, walk) ];
        },
        "if": function(conditional, t, e) {
            return [ this[0], walk(conditional), walk(t), walk(e) ];
        },
        "for": function(init, cond, step, block) {
            return [ this[0], walk(init), walk(cond), walk(step), walk(block) ];
        },
        "for-in": function(vvar, key, hash, block) {
            return [ this[0], walk(vvar), walk(key), walk(hash), walk(block) ];
        },
        "while": function(cond, block) {
            return [ this[0], walk(cond), walk(block) ];
        },
        "do": function(cond, block) {
            return [ this[0], walk(cond), walk(block) ];
        },
        "return": function(expr) {
            return [ this[0], walk(expr) ];
        },
        "binary": function(op, left, right) {
            return [ this[0], op, walk(left), walk(right) ];
        },
        "unary-prefix": function(op, expr) {
            return [ this[0], op, walk(expr) ];
        },
        "unary-postfix": function(op, expr) {
            return [ this[0], op, walk(expr) ];
        },
        "sub": function(expr, subscript) {
            return [ this[0], walk(expr), walk(subscript) ];
        },
        "object": function(props) {
            return [ this[0], MAP(props, function(p){
                return p.length == 2
                    ? [ p[0], walk(p[1]) ]
                    : [ p[0], walk(p[1]), p[2] ]; // get/set-ter
            }) ];
        },
        "regexp": function(rx, mods) {
            return [ this[0], rx, mods ];
        },
        "array": function(elements) {
            return [ this[0], MAP(elements, walk) ];
        },
        "stat": function(stat) {
            return [ this[0], walk(stat) ];
        },
        "seq": function() {
            return [ this[0] ].concat(MAP(slice(arguments), walk));
        },
        "label": function(name, block) {
            return [ this[0], name, walk(block) ];
        },
        "with": function(expr, block) {
            return [ this[0], walk(expr), walk(block) ];
        },
        "atom": function(name) {
            return [ this[0], name ];
        },
        "directive": function(dir) {
            return [ this[0], dir ];
        }
    };

    var user = {};
    var stack = [];
    function walk(ast) {
        if (ast == null)
            return null;
        try {
            stack.push(ast);
            var type = ast[0];
            var gen = user[type];
            if (gen) {
                var ret = gen.apply(ast, ast.slice(1));
                if (ret != null)
                    return ret;
            }
            gen = walkers[type];
            return gen.apply(ast, ast.slice(1));
        } finally {
            stack.pop();
        }
    };

    function dive(ast) {
        if (ast == null)
            return null;
        try {
            stack.push(ast);
            return walkers[ast[0]].apply(ast, ast.slice(1));
        } finally {
            stack.pop();
        }
    };

    function with_walkers(walkers, cont){
        var save = {}, i;
        for (i in walkers) if (HOP(walkers, i)) {
            save[i] = user[i];
            user[i] = walkers[i];
        }
        var ret = cont();
        for (i in save) if (HOP(save, i)) {
            if (!save[i]) delete user[i];
            else user[i] = save[i];
        }
        return ret;
    };

    return {
        walk: walk,
        dive: dive,
        with_walkers: with_walkers,
        parent: function() {
            return stack[stack.length - 2]; // last one is current node
        },
        stack: function() {
            return stack;
        }
    };
};

/* -----[ Scope and mangling ]----- */

function Scope(parent) {
    this.names = {};        // names defined in this scope
    this.mangled = {};      // mangled names (orig.name => mangled)
    this.rev_mangled = {};  // reverse lookup (mangled => orig.name)
    this.cname = -1;        // current mangled name
    this.refs = {};         // names referenced from this scope
    this.uses_with = false; // will become TRUE if with() is detected in this or any subscopes
    this.uses_eval = false; // will become TRUE if eval() is detected in this or any subscopes
    this.directives = [];   // directives activated from this scope
    this.parent = parent;   // parent scope
    this.children = [];     // sub-scopes
    if (parent) {
        this.level = parent.level + 1;
        parent.children.push(this);
    } else {
        this.level = 0;
    }
};

function base54_digits() {
    if (typeof DIGITS_OVERRIDE_FOR_TESTING != "undefined")
        return DIGITS_OVERRIDE_FOR_TESTING;
    else
        return ["ʕʘ‿ʘʔ", "ʕʘ̅͜ʘ̅ʔ", "ᶘᵒᴥᵒᶅ", "ᶘᵔᴥᵔᶅ", "ʕథ౪థʔ", "ᶘᵕˑ̫ᵕᶅ", "ʘ̥ꀾʘ̥", "ಠʖ̯ಠ", "ಠ益ಠ", "ಥ_ಠೃ", "ʘ̅ㅈʘ̅", "ಠิ﹏ಠิ", "ᵒ̌ૢཪᵒ̌ૢ", "ఠ_ఠ"];
}

var base54 = (function(){
    var DIGITS = base54_digits();
    for(var j, x, i = DIGITS.length; i; j = Math.floor(Math.random() * i), x = DIGITS[--i], DIGITS[i] = DIGITS[j], DIGITS[j] = x);
    return function(num) {
        var ret = "", base = DIGITS.length;
        do {
            ret += DIGITS[num % base];
            num = Math.floor(num / base);
            base = DIGITS.length;
        } while (num > 0);
        return ret;
    };
})();

Scope.prototype = {
    has: function(name) {
        for (var s = this; s; s = s.parent)
            if (HOP(s.names, name))
                return s;
    },
    has_mangled: function(mname) {
        for (var s = this; s; s = s.parent)
            if (HOP(s.rev_mangled, mname))
                return s;
    },
    toJSON: function() {
        return {
            names: this.names,
            uses_eval: this.uses_eval,
            uses_with: this.uses_with
        };
    },

    next_mangled: function() {
        // we must be careful that the new mangled name:
        //
        // 1. doesn't shadow a mangled name from a parent
        //    scope, unless we don't reference the original
        //    name from this scope OR from any sub-scopes!
        //    This will get slow.
        //
        // 2. doesn't shadow an original name from a parent
        //    scope, in the event that the name is not mangled
        //    in the parent scope and we reference that name
        //    here OR IN ANY SUBSCOPES!
        //
        // 3. doesn't shadow a name that is referenced but not
        //    defined (possibly global defined elsewhere).
        for (;;) {
            var m = base54(++this.cname), prior;

            // case 1.
            prior = this.has_mangled(m);
            if (prior && this.refs[prior.rev_mangled[m]] === prior)
                continue;

            // case 2.
            prior = this.has(m);
            if (prior && prior !== this && this.refs[m] === prior && !prior.has_mangled(m))
                continue;

            // case 3.
            if (HOP(this.refs, m) && this.refs[m] == null)
                continue;

            // I got "do" once. :-/
            if (!is_identifier(m))
                continue;

            return m;
        }
    },
    set_mangle: function(name, m) {
        this.rev_mangled[m] = name;
        return this.mangled[name] = m;
    },
    get_mangled: function(name, newMangle) {
        if (this.uses_eval || this.uses_with) return name; // no mangle if eval or with is in use
        var s = this.has(name);
        if (!s) return name; // not in visible scope, no mangle
        if (HOP(s.mangled, name)) return s.mangled[name]; // already mangled in this scope
        if (!newMangle) return name;                      // not found and no mangling requested
        return s.set_mangle(name, s.next_mangled());
    },
    references: function(name) {
        return name && !this.parent || this.uses_with || this.uses_eval || this.refs[name];
    },
    define: function(name, type) {
        if (name != null) {
            if (type == "var" || !HOP(this.names, name))
                this.names[name] = type || "var";
            return name;
        }
    },
    active_directive: function(dir) {
        return member(dir, this.directives) || this.parent && this.parent.active_directive(dir);
    }
};

function ast_add_scope(ast) {

    var current_scope = null;
    var w = ast_walker(), walk = w.walk;
    var having_eval = [];

    function with_new_scope(cont) {
        current_scope = new Scope(current_scope);
        current_scope.labels = new Scope();
        var ret = current_scope.body = cont();
        ret.scope = current_scope;
        current_scope = current_scope.parent;
        return ret;
    };

    function define(name, type) {
        return current_scope.define(name, type);
    };

    function reference(name) {
        current_scope.refs[name] = true;
    };

    function _lambda(name, args, body) {
        var is_defun = this[0] == "defun";
        return [ this[0], is_defun ? define(name, "defun") : name, args, with_new_scope(function(){
            if (!is_defun) define(name, "lambda");
            MAP(args, function(name){ define(name, "arg") });
            return MAP(body, walk);
        })];
    };

    function _vardefs(type) {
        return function(defs) {
            MAP(defs, function(d){
                define(d[0], type);
                if (d[1]) reference(d[0]);
            });
        };
    };

    function _breacont(label) {
        if (label)
            current_scope.labels.refs[label] = true;
    };

    return with_new_scope(function(){
        // process AST
        var ret = w.with_walkers({
            "function": _lambda,
            "defun": _lambda,
            "label": function(name, stat) { current_scope.labels.define(name) },
            "break": _breacont,
            "continue": _breacont,
            "with": function(expr, block) {
                for (var s = current_scope; s; s = s.parent)
                    s.uses_with = true;
            },
            "var": _vardefs("var"),
            "const": _vardefs("const"),
            "try": function(t, c, f) {
                if (c != null) return [
                    this[0],
                    MAP(t, walk),
                    [ define(c[0], "catch"), MAP(c[1], walk) ],
                    f != null ? MAP(f, walk) : null
                ];
            },
            "name": function(name) {
                if (name == "eval")
                    having_eval.push(current_scope);
                reference(name);
            }
        }, function(){
            return walk(ast);
        });

        // the reason why we need an additional pass here is
        // that names can be used prior to their definition.

        // scopes where eval was detected and their parents
        // are marked with uses_eval, unless they define the
        // "eval" name.
        MAP(having_eval, function(scope){
            if (!scope.has("eval")) while (scope) {
                scope.uses_eval = true;
                scope = scope.parent;
            }
        });

        // for referenced names it might be useful to know
        // their origin scope.  current_scope here is the
        // toplevel one.
        function fixrefs(scope, i) {
            // do children first; order shouldn't matter
            for (i = scope.children.length; --i >= 0;)
                fixrefs(scope.children[i]);
            for (i in scope.refs) if (HOP(scope.refs, i)) {
                // find origin scope and propagate the reference to origin
                for (var origin = scope.has(i), s = scope; s; s = s.parent) {
                    s.refs[i] = origin;
                    if (s === origin) break;
                }
            }
        };
        fixrefs(current_scope);

        return ret;
    });

};

/* -----[ mangle names ]----- */

function ast_mangle(ast, options) {
    var w = ast_walker(), walk = w.walk, scope;
    options = defaults(options, {
        mangle       : true,
        toplevel     : false,
        defines      : null,
        except       : null,
        no_functions : false
    });

    function get_mangled(name, newMangle) {
        if (!options.mangle) return name;
        if (!options.toplevel && !scope.parent) return name; // don't mangle toplevel
        if (options.except && member(name, options.except))
            return name;
        if (options.no_functions && HOP(scope.names, name) &&
            (scope.names[name] == 'defun' || scope.names[name] == 'lambda'))
            return name;
        return scope.get_mangled(name, newMangle);
    };

    function get_define(name) {
        if (options.defines) {
            // we always lookup a defined symbol for the current scope FIRST, so declared
            // vars trump a DEFINE symbol, but if no such var is found, then match a DEFINE value
            if (!scope.has(name)) {
                if (HOP(options.defines, name)) {
                    return options.defines[name];
                }
            }
            return null;
        }
    };

    function _lambda(name, args, body) {
        if (!options.no_functions && options.mangle) {
            var is_defun = this[0] == "defun", extra;
            if (name) {
                if (is_defun) name = get_mangled(name);
                else if (body.scope.references(name)) {
                    extra = {};
                    if (!(scope.uses_eval || scope.uses_with))
                        name = extra[name] = scope.next_mangled();
                    else
                        extra[name] = name;
                }
                else name = null;
            }
        }
        body = with_scope(body.scope, function(){
            args = MAP(args, function(name){ return get_mangled(name) });
            return MAP(body, walk);
        }, extra);
        return [ this[0], name, args, body ];
    };

    function with_scope(s, cont, extra) {
        var _scope = scope;
        scope = s;
        if (extra) for (var i in extra) if (HOP(extra, i)) {
            s.set_mangle(i, extra[i]);
        }
        for (var i in s.names) if (HOP(s.names, i)) {
            get_mangled(i, true);
        }
        var ret = cont();
        ret.scope = s;
        scope = _scope;
        return ret;
    };

    function _vardefs(defs) {
        return [ this[0], MAP(defs, function(d){
            return [ get_mangled(d[0]), walk(d[1]) ];
        }) ];
    };

    function _breacont(label) {
        if (label) return [ this[0], scope.labels.get_mangled(label) ];
    };

    return w.with_walkers({
        "function": _lambda,
        "defun": function() {
            // move function declarations to the top when
            // they are not in some block.
            var ast = _lambda.apply(this, arguments);
            switch (w.parent()[0]) {
              case "toplevel":
              case "function":
              case "defun":
                return MAP.at_top(ast);
            }
            return ast;
        },
        "label": function(label, stat) {
            if (scope.labels.refs[label]) return [
                this[0],
                scope.labels.get_mangled(label, true),
                walk(stat)
            ];
            return walk(stat);
        },
        "break": _breacont,
        "continue": _breacont,
        "var": _vardefs,
        "const": _vardefs,
        "name": function(name) {
            return get_define(name) || [ this[0], get_mangled(name) ];
        },
        "try": function(t, c, f) {
            return [ this[0],
                     MAP(t, walk),
                     c != null ? [ get_mangled(c[0]), MAP(c[1], walk) ] : null,
                     f != null ? MAP(f, walk) : null ];
        },
        "toplevel": function(body) {
            var self = this;
            return with_scope(self.scope, function(){
                return [ self[0], MAP(body, walk) ];
            });
        },
        "directive": function() {
            return MAP.at_top(this);
        }
    }, function() {
        return walk(ast_add_scope(ast));
    });
};

/* -----[
   - compress foo["bar"] into foo.bar,
   - remove block brackets {} where possible
   - join consecutive var declarations
   - various optimizations for IFs:
   - if (cond) foo(); else bar();  ==>  cond?foo():bar();
   - if (cond) foo();  ==>  cond&&foo();
   - if (foo) return bar(); else return baz();  ==> return foo?bar():baz(); // also for throw
   - if (foo) return bar(); else something();  ==> {if(foo)return bar();something()}
   ]----- */

var warn = function(){};

function best_of(ast1, ast2) {
    return gen_code(ast1).length > gen_code(ast2[0] == "stat" ? ast2[1] : ast2).length ? ast2 : ast1;
};

function last_stat(b) {
    if (b[0] == "block" && b[1] && b[1].length > 0)
        return b[1][b[1].length - 1];
    return b;
}

function aborts(t) {
    if (t) switch (last_stat(t)[0]) {
      case "return":
      case "break":
      case "continue":
      case "throw":
        return true;
    }
};

function boolean_expr(expr) {
    return ( (expr[0] == "unary-prefix"
              && member(expr[1], [ "!", "delete" ])) ||

             (expr[0] == "binary"
              && member(expr[1], [ "in", "instanceof", "==", "!=", "===", "!==", "<", "<=", ">=", ">" ])) ||

             (expr[0] == "binary"
              && member(expr[1], [ "&&", "||" ])
              && boolean_expr(expr[2])
              && boolean_expr(expr[3])) ||

             (expr[0] == "conditional"
              && boolean_expr(expr[2])
              && boolean_expr(expr[3])) ||

             (expr[0] == "assign"
              && expr[1] === true
              && boolean_expr(expr[3])) ||

             (expr[0] == "seq"
              && boolean_expr(expr[expr.length - 1]))
           );
};

function empty(b) {
    return !b || (b[0] == "block" && (!b[1] || b[1].length == 0));
};

function is_string(node) {
    return (node[0] == "string" ||
            node[0] == "unary-prefix" && node[1] == "typeof" ||
            node[0] == "binary" && node[1] == "+" &&
            (is_string(node[2]) || is_string(node[3])));
};

var when_constant = (function(){

    var $NOT_CONSTANT = {};

    // this can only evaluate constant expressions.  If it finds anything
    // not constant, it throws $NOT_CONSTANT.
    function evaluate(expr) {
        switch (expr[0]) {
          case "string":
          case "num":
            return expr[1];
          case "name":
          case "atom":
            switch (expr[1]) {
              case "true": return true;
              case "false": return false;
              case "null": return null;
            }
            break;
          case "unary-prefix":
            switch (expr[1]) {
              case "!": return !evaluate(expr[2]);
              case "typeof": return typeof evaluate(expr[2]);
              case "~": return ~evaluate(expr[2]);
              case "-": return -evaluate(expr[2]);
              case "+": return +evaluate(expr[2]);
            }
            break;
          case "binary":
            var left = expr[2], right = expr[3];
            switch (expr[1]) {
              case "&&"         : return evaluate(left) &&         evaluate(right);
              case "||"         : return evaluate(left) ||         evaluate(right);
              case "|"          : return evaluate(left) |          evaluate(right);
              case "&"          : return evaluate(left) &          evaluate(right);
              case "^"          : return evaluate(left) ^          evaluate(right);
              case "+"          : return evaluate(left) +          evaluate(right);
              case "*"          : return evaluate(left) *          evaluate(right);
              case "/"          : return evaluate(left) /          evaluate(right);
              case "%"          : return evaluate(left) %          evaluate(right);
              case "-"          : return evaluate(left) -          evaluate(right);
              case "<<"         : return evaluate(left) <<         evaluate(right);
              case ">>"         : return evaluate(left) >>         evaluate(right);
              case ">>>"        : return evaluate(left) >>>        evaluate(right);
              case "=="         : return evaluate(left) ==         evaluate(right);
              case "==="        : return evaluate(left) ===        evaluate(right);
              case "!="         : return evaluate(left) !=         evaluate(right);
              case "!=="        : return evaluate(left) !==        evaluate(right);
              case "<"          : return evaluate(left) <          evaluate(right);
              case "<="         : return evaluate(left) <=         evaluate(right);
              case ">"          : return evaluate(left) >          evaluate(right);
              case ">="         : return evaluate(left) >=         evaluate(right);
              case "in"         : return evaluate(left) in         evaluate(right);
              case "instanceof" : return evaluate(left) instanceof evaluate(right);
            }
        }
        throw $NOT_CONSTANT;
    };

    return function(expr, yes, no) {
        try {
            var val = evaluate(expr), ast;
            switch (typeof val) {
              case "string": ast =  [ "string", val ]; break;
              case "number": ast =  [ "num", val ]; break;
              case "boolean": ast =  [ "name", String(val) ]; break;
              default:
                if (val === null) { ast = [ "atom", "null" ]; break; }
                throw new Error("Can't handle constant of type: " + (typeof val));
            }
            return yes.call(expr, ast, val);
        } catch(ex) {
            if (ex === $NOT_CONSTANT) {
                if (expr[0] == "binary"
                    && (expr[1] == "===" || expr[1] == "!==")
                    && ((is_string(expr[2]) && is_string(expr[3]))
                        || (boolean_expr(expr[2]) && boolean_expr(expr[3])))) {
                    expr[1] = expr[1].substr(0, 2);
                }
                else if (no && expr[0] == "binary"
                         && (expr[1] == "||" || expr[1] == "&&")) {
                    // the whole expression is not constant but the lval may be...
                    try {
                        var lval = evaluate(expr[2]);
                        expr = ((expr[1] == "&&" && (lval ? expr[3] : lval))    ||
                                (expr[1] == "||" && (lval ? lval    : expr[3])) ||
                                expr);
                    } catch(ex2) {
                        // IGNORE... lval is not constant
                    }
                }
                return no ? no.call(expr, expr) : null;
            }
            else throw ex;
        }
    };

})();

function warn_unreachable(ast) {
    if (!empty(ast))
        warn("Dropping unreachable code: " + gen_code(ast, true));
};

function prepare_ifs(ast) {
    var w = ast_walker(), walk = w.walk;
    // In this first pass, we rewrite ifs which abort with no else with an
    // if-else.  For example:
    //
    // if (x) {
    //     blah();
    //     return y;
    // }
    // foobar();
    //
    // is rewritten into:
    //
    // if (x) {
    //     blah();
    //     return y;
    // } else {
    //     foobar();
    // }
    function redo_if(statements) {
        statements = MAP(statements, walk);

        for (var i = 0; i < statements.length; ++i) {
            var fi = statements[i];
            if (fi[0] != "if") continue;

            if (fi[3]) continue;

            var t = fi[2];
            if (!aborts(t)) continue;

            var conditional = walk(fi[1]);

            var e_body = redo_if(statements.slice(i + 1));
            var e = e_body.length == 1 ? e_body[0] : [ "block", e_body ];

            return statements.slice(0, i).concat([ [
                fi[0],          // "if"
                conditional,    // conditional
                t,              // then
                e               // else
            ] ]);
        }

        return statements;
    };

    function redo_if_lambda(name, args, body) {
        body = redo_if(body);
        return [ this[0], name, args, body ];
    };

    function redo_if_block(statements) {
        return [ this[0], statements != null ? redo_if(statements) : null ];
    };

    return w.with_walkers({
        "defun": redo_if_lambda,
        "function": redo_if_lambda,
        "block": redo_if_block,
        "splice": redo_if_block,
        "toplevel": function(statements) {
            return [ this[0], redo_if(statements) ];
        },
        "try": function(t, c, f) {
            return [
                this[0],
                redo_if(t),
                c != null ? [ c[0], redo_if(c[1]) ] : null,
                f != null ? redo_if(f) : null
            ];
        }
    }, function() {
        return walk(ast);
    });
};

function for_side_effects(ast, handler) {
    var w = ast_walker(), walk = w.walk;
    var $stop = {}, $restart = {};
    function stop() { throw $stop };
    function restart() { throw $restart };
    function found(){ return handler.call(this, this, w, stop, restart) };
    function unary(op) {
        if (op == "++" || op == "--")
            return found.apply(this, arguments);
    };
    function binary(op) {
        if (op == "&&" || op == "||")
            return found.apply(this, arguments);
    };
    return w.with_walkers({
        "try": found,
        "throw": found,
        "return": found,
        "new": found,
        "switch": found,
        "break": found,
        "continue": found,
        "assign": found,
        "call": found,
        "if": found,
        "for": found,
        "for-in": found,
        "while": found,
        "do": found,
        "unary-prefix": unary,
        "unary-postfix": unary,
        "conditional": found,
        "binary": binary,
        "defun": found
    }, function(){
        while (true) try {
            walk(ast);
            break;
        } catch(ex) {
            if (ex === $stop) break;
            if (ex === $restart) continue;
            throw ex;
        }
    });
};

function ast_lift_variables(ast) {
    var w = ast_walker(), walk = w.walk, scope;
    function do_body(body, env) {
        var _scope = scope;
        scope = env;
        body = MAP(body, walk);
        var hash = {}, names = MAP(env.names, function(type, name){
            if (type != "var") return MAP.skip;
            if (!env.references(name)) return MAP.skip;
            hash[name] = true;
            return [ name ];
        });
        if (names.length > 0) {
            // looking for assignments to any of these variables.
            // we can save considerable space by moving the definitions
            // in the var declaration.
            for_side_effects([ "block", body ], function(ast, walker, stop, restart) {
                if (ast[0] == "assign"
                    && ast[1] === true
                    && ast[2][0] == "name"
                    && HOP(hash, ast[2][1])) {
                    // insert the definition into the var declaration
                    for (var i = names.length; --i >= 0;) {
                        if (names[i][0] == ast[2][1]) {
                            if (names[i][1]) // this name already defined, we must stop
                                stop();
                            names[i][1] = ast[3]; // definition
                            names.push(names.splice(i, 1)[0]);
                            break;
                        }
                    }
                    // remove this assignment from the AST.
                    var p = walker.parent();
                    if (p[0] == "seq") {
                        var a = p[2];
                        a.unshift(0, p.length);
                        p.splice.apply(p, a);
                    }
                    else if (p[0] == "stat") {
                        p.splice(0, p.length, "block"); // empty statement
                    }
                    else {
                        stop();
                    }
                    restart();
                }
                stop();
            });
            body.unshift([ "var", names ]);
        }
        scope = _scope;
        return body;
    };
    function _vardefs(defs) {
        var ret = null;
        for (var i = defs.length; --i >= 0;) {
            var d = defs[i];
            if (!d[1]) continue;
            d = [ "assign", true, [ "name", d[0] ], d[1] ];
            if (ret == null) ret = d;
            else ret = [ "seq", d, ret ];
        }
        if (ret == null && w.parent()[0] != "for") {
            if (w.parent()[0] == "for-in")
                return [ "name", defs[0][0] ];
            return MAP.skip;
        }
        return [ "stat", ret ];
    };
    function _toplevel(body) {
        return [ this[0], do_body(body, this.scope) ];
    };
    return w.with_walkers({
        "function": function(name, args, body){
            for (var i = args.length; --i >= 0 && !body.scope.references(args[i]);)
                args.pop();
            if (!body.scope.references(name)) name = null;
            return [ this[0], name, args, do_body(body, body.scope) ];
        },
        "defun": function(name, args, body){
            if (!scope.references(name)) return MAP.skip;
            for (var i = args.length; --i >= 0 && !body.scope.references(args[i]);)
                args.pop();
            return [ this[0], name, args, do_body(body, body.scope) ];
        },
        "var": _vardefs,
        "toplevel": _toplevel
    }, function(){
        return walk(ast_add_scope(ast));
    });
};

function ast_squeeze(ast, options) {
    ast = squeeze_1(ast, options);
    ast = squeeze_2(ast, options);
    return ast;
};

function squeeze_1(ast, options) {
    options = defaults(options, {
        make_seqs   : true,
        dead_code   : true,
        no_warnings : false,
        keep_comps  : true,
        unsafe      : false
    });

    var w = ast_walker(), walk = w.walk, scope;

    function negate(c) {
        var not_c = [ "unary-prefix", "!", c ];
        switch (c[0]) {
          case "unary-prefix":
            return c[1] == "!" && boolean_expr(c[2]) ? c[2] : not_c;
          case "seq":
            c = slice(c);
            c[c.length - 1] = negate(c[c.length - 1]);
            return c;
          case "conditional":
            return best_of(not_c, [ "conditional", c[1], negate(c[2]), negate(c[3]) ]);
          case "binary":
            var op = c[1], left = c[2], right = c[3];
            if (!options.keep_comps) switch (op) {
              case "<="  : return [ "binary", ">", left, right ];
              case "<"   : return [ "binary", ">=", left, right ];
              case ">="  : return [ "binary", "<", left, right ];
              case ">"   : return [ "binary", "<=", left, right ];
            }
            switch (op) {
              case "=="  : return [ "binary", "!=", left, right ];
              case "!="  : return [ "binary", "==", left, right ];
              case "===" : return [ "binary", "!==", left, right ];
              case "!==" : return [ "binary", "===", left, right ];
              case "&&"  : return best_of(not_c, [ "binary", "||", negate(left), negate(right) ]);
              case "||"  : return best_of(not_c, [ "binary", "&&", negate(left), negate(right) ]);
            }
            break;
        }
        return not_c;
    };

    function make_conditional(c, t, e) {
        var make_real_conditional = function() {
            if (c[0] == "unary-prefix" && c[1] == "!") {
                return e ? [ "conditional", c[2], e, t ] : [ "binary", "||", c[2], t ];
            } else {
                return e ? best_of(
                    [ "conditional", c, t, e ],
                    [ "conditional", negate(c), e, t ]
                ) : [ "binary", "&&", c, t ];
            }
        };
        // shortcut the conditional if the expression has a constant value
        return when_constant(c, function(ast, val){
            warn_unreachable(val ? e : t);
            return          (val ? t : e);
        }, make_real_conditional);
    };

    function rmblock(block) {
        if (block != null && block[0] == "block" && block[1]) {
            if (block[1].length == 1)
                block = block[1][0];
            else if (block[1].length == 0)
                block = [ "block" ];
        }
        return block;
    };

    function _lambda(name, args, body) {
        return [ this[0], name, args, tighten(body, "lambda") ];
    };

    // this function does a few things:
    // 1. discard useless blocks
    // 2. join consecutive var declarations
    // 3. remove obviously dead code
    // 4. transform consecutive statements using the comma operator
    // 5. if block_type == "lambda" and it detects constructs like if(foo) return ... - rewrite like if (!foo) { ... }
    function tighten(statements, block_type) {
        statements = MAP(statements, walk);

        statements = statements.reduce(function(a, stat){
            if (stat[0] == "block") {
                if (stat[1]) {
                    a.push.apply(a, stat[1]);
                }
            } else {
                a.push(stat);
            }
            return a;
        }, []);

        statements = (function(a, prev){
            statements.forEach(function(cur){
                if (prev && ((cur[0] == "var" && prev[0] == "var") ||
                             (cur[0] == "const" && prev[0] == "const"))) {
                    prev[1] = prev[1].concat(cur[1]);
                } else {
                    a.push(cur);
                    prev = cur;
                }
            });
            return a;
        })([]);

        if (options.dead_code) statements = (function(a, has_quit){
            statements.forEach(function(st){
                if (has_quit) {
                    if (st[0] == "function" || st[0] == "defun") {
                        a.push(st);
                    }
                    else if (st[0] == "var" || st[0] == "const") {
                        if (!options.no_warnings)
                            warn("Variables declared in unreachable code");
                        st[1] = MAP(st[1], function(def){
                            if (def[1] && !options.no_warnings)
                                warn_unreachable([ "assign", true, [ "name", def[0] ], def[1] ]);
                            return [ def[0] ];
                        });
                        a.push(st);
                    }
                    else if (!options.no_warnings)
                        warn_unreachable(st);
                }
                else {
                    a.push(st);
                    if (member(st[0], [ "return", "throw", "break", "continue" ]))
                        has_quit = true;
                }
            });
            return a;
        })([]);

        if (options.make_seqs) statements = (function(a, prev) {
            statements.forEach(function(cur){
                if (prev && prev[0] == "stat" && cur[0] == "stat") {
                    prev[1] = [ "seq", prev[1], cur[1] ];
                } else {
                    a.push(cur);
                    prev = cur;
                }
            });
            if (a.length >= 2
                && a[a.length-2][0] == "stat"
                && (a[a.length-1][0] == "return" || a[a.length-1][0] == "throw")
                && a[a.length-1][1])
            {
                a.splice(a.length - 2, 2,
                         [ a[a.length-1][0],
                           [ "seq", a[a.length-2][1], a[a.length-1][1] ]]);
            }
            return a;
        })([]);

        // this increases jQuery by 1K.  Probably not such a good idea after all..
        // part of this is done in prepare_ifs anyway.
        // if (block_type == "lambda") statements = (function(i, a, stat){
        //         while (i < statements.length) {
        //                 stat = statements[i++];
        //                 if (stat[0] == "if" && !stat[3]) {
        //                         if (stat[2][0] == "return" && stat[2][1] == null) {
        //                                 a.push(make_if(negate(stat[1]), [ "block", statements.slice(i) ]));
        //                                 break;
        //                         }
        //                         var last = last_stat(stat[2]);
        //                         if (last[0] == "return" && last[1] == null) {
        //                                 a.push(make_if(stat[1], [ "block", stat[2][1].slice(0, -1) ], [ "block", statements.slice(i) ]));
        //                                 break;
        //                         }
        //                 }
        //                 a.push(stat);
        //         }
        //         return a;
        // })(0, []);

        return statements;
    };

    function make_if(c, t, e) {
        return when_constant(c, function(ast, val){
            if (val) {
                t = walk(t);
                warn_unreachable(e);
                return t || [ "block" ];
            } else {
                e = walk(e);
                warn_unreachable(t);
                return e || [ "block" ];
            }
        }, function() {
            return make_real_if(c, t, e);
        });
    };

    function abort_else(c, t, e) {
        var ret = [ [ "if", negate(c), e ] ];
        if (t[0] == "block") {
            if (t[1]) ret = ret.concat(t[1]);
        } else {
            ret.push(t);
        }
        return walk([ "block", ret ]);
    };

    function make_real_if(c, t, e) {
        c = walk(c);
        t = walk(t);
        e = walk(e);

        if (empty(e) && empty(t))
            return [ "stat", c ];

        if (empty(t)) {
            c = negate(c);
            t = e;
            e = null;
        } else if (empty(e)) {
            e = null;
        } else {
            // if we have both else and then, maybe it makes sense to switch them?
            (function(){
                var a = gen_code(c);
                var n = negate(c);
                var b = gen_code(n);
                if (b.length < a.length) {
                    var tmp = t;
                    t = e;
                    e = tmp;
                    c = n;
                }
            })();
        }
        var ret = [ "if", c, t, e ];
        if (t[0] == "if" && empty(t[3]) && empty(e)) {
            ret = best_of(ret, walk([ "if", [ "binary", "&&", c, t[1] ], t[2] ]));
        }
        else if (t[0] == "stat") {
            if (e) {
                if (e[0] == "stat")
                    ret = best_of(ret, [ "stat", make_conditional(c, t[1], e[1]) ]);
                else if (aborts(e))
                    ret = abort_else(c, t, e);
            }
            else {
                ret = best_of(ret, [ "stat", make_conditional(c, t[1]) ]);
            }
        }
        else if (e && t[0] == e[0] && (t[0] == "return" || t[0] == "throw") && t[1] && e[1]) {
            ret = best_of(ret, [ t[0], make_conditional(c, t[1], e[1] ) ]);
        }
        else if (e && aborts(t)) {
            ret = [ [ "if", c, t ] ];
            if (e[0] == "block") {
                if (e[1]) ret = ret.concat(e[1]);
            }
            else {
                ret.push(e);
            }
            ret = walk([ "block", ret ]);
        }
        else if (t && aborts(e)) {
            ret = abort_else(c, t, e);
        }
        return ret;
    };

    function _do_while(cond, body) {
        return when_constant(cond, function(cond, val){
            if (!val) {
                warn_unreachable(body);
                return [ "block" ];
            } else {
                return [ "for", null, null, null, walk(body) ];
            }
        });
    };

    return w.with_walkers({
        "sub": function(expr, subscript) {
            if (subscript[0] == "string") {
                var name = subscript[1];
                if (is_identifier(name))
                    return [ "dot", walk(expr), name ];
                else if (/^[1-9][0-9]*$/.test(name) || name === "0")
                    return [ "sub", walk(expr), [ "num", parseInt(name, 10) ] ];
            }
        },
        "if": make_if,
        "toplevel": function(body) {
            return [ "toplevel", tighten(body) ];
        },
        "switch": function(expr, body) {
            var last = body.length - 1;
            return [ "switch", walk(expr), MAP(body, function(branch, i){
                var block = tighten(branch[1]);
                if (i == last && block.length > 0) {
                    var node = block[block.length - 1];
                    if (node[0] == "break" && !node[1])
                        block.pop();
                }
                return [ branch[0] ? walk(branch[0]) : null, block ];
            }) ];
        },
        "function": _lambda,
        "defun": _lambda,
        "block": function(body) {
            if (body) return rmblock([ "block", tighten(body) ]);
        },
        "binary": function(op, left, right) {
            return when_constant([ "binary", op, walk(left), walk(right) ], function yes(c){
                return best_of(walk(c), this);
            }, function no() {
                return function(){
                    if(op != "==" && op != "!=") return;
                    var l = walk(left), r = walk(right);
                    if(l && l[0] == "unary-prefix" && l[1] == "!" && l[2][0] == "num")
                        left = ['num', +!l[2][1]];
                    else if (r && r[0] == "unary-prefix" && r[1] == "!" && r[2][0] == "num")
                        right = ['num', +!r[2][1]];
                    return ["binary", op, left, right];
                }() || this;
            });
        },
        "conditional": function(c, t, e) {
            return make_conditional(walk(c), walk(t), walk(e));
        },
        "try": function(t, c, f) {
            return [
                "try",
                tighten(t),
                c != null ? [ c[0], tighten(c[1]) ] : null,
                f != null ? tighten(f) : null
            ];
        },
        "unary-prefix": function(op, expr) {
            expr = walk(expr);
            var ret = [ "unary-prefix", op, expr ];
            if (op == "!")
                ret = best_of(ret, negate(expr));
            return when_constant(ret, function(ast, val){
                return walk(ast); // it's either true or false, so minifies to !0 or !1
            }, function() { return ret });
        },
        "name": function(name) {
            switch (name) {
              case "true": return [ "unary-prefix", "!", [ "num", 0 ]];
              case "false": return [ "unary-prefix", "!", [ "num", 1 ]];
            }
        },
        "while": _do_while,
        "assign": function(op, lvalue, rvalue) {
            lvalue = walk(lvalue);
            rvalue = walk(rvalue);
            var okOps = [ '+', '-', '/', '*', '%', '>>', '<<', '>>>', '|', '^', '&' ];
            if (op === true && lvalue[0] === "name" && rvalue[0] === "binary" &&
                ~okOps.indexOf(rvalue[1]) && rvalue[2][0] === "name" &&
                rvalue[2][1] === lvalue[1]) {
                return [ this[0], rvalue[1], lvalue, rvalue[3] ]
            }
            return [ this[0], op, lvalue, rvalue ];
        },
        "call": function(expr, args) {
            expr = walk(expr);
            if (options.unsafe && expr[0] == "dot" && expr[1][0] == "string" && expr[2] == "toString") {
                return expr[1];
            }
            return [ this[0], expr,  MAP(args, walk) ];
        },
        "num": function (num) {
            if (!isFinite(num))
                return [ "binary", "/", num === 1 / 0
                         ? [ "num", 1 ] : num === -1 / 0
                         ? [ "unary-prefix", "-", [ "num", 1 ] ]
                         : [ "num", 0 ], [ "num", 0 ] ];

            return [ this[0], num ];
        }
    }, function() {
        return walk(prepare_ifs(walk(prepare_ifs(ast))));
    });
};

function squeeze_2(ast, options) {
    var w = ast_walker(), walk = w.walk, scope;
    function with_scope(s, cont) {
        var save = scope, ret;
        scope = s;
        ret = cont();
        scope = save;
        return ret;
    };
    function lambda(name, args, body) {
        return [ this[0], name, args, with_scope(body.scope, curry(MAP, body, walk)) ];
    };
    return w.with_walkers({
        "directive": function(dir) {
            if (scope.active_directive(dir))
                return [ "block" ];
            scope.directives.push(dir);
        },
        "toplevel": function(body) {
            return [ this[0], with_scope(this.scope, curry(MAP, body, walk)) ];
        },
        "function": lambda,
        "defun": lambda
    }, function(){
        return walk(ast_add_scope(ast));
    });
};

/* -----[ re-generate code from the AST ]----- */

var DOT_CALL_NO_PARENS = jsp.array_to_hash([
    "name",
    "array",
    "object",
    "string",
    "dot",
    "sub",
    "call",
    "regexp",
    "defun"
]);

function make_string(str, ascii_only) {
    var dq = 0, sq = 0;
    str = str.replace(/[\\\b\f\n\r\t\x22\x27\u2028\u2029\0]/g, function(s){
        switch (s) {
          case "\\": return "\\\\";
          case "\b": return "\\b";
          case "\f": return "\\f";
          case "\n": return "\\n";
          case "\r": return "\\r";
          case "\u2028": return "\\u2028";
          case "\u2029": return "\\u2029";
          case '"': ++dq; return '"';
          case "'": ++sq; return "'";
          case "\0": return "\\0";
        }
        return s;
    });
    if (ascii_only) str = to_ascii(str);
    if (dq > sq) return "'" + str.replace(/\x27/g, "\\'") + "'";
    else return '"' + str.replace(/\x22/g, '\\"') + '"';
};

function to_ascii(str) {
    return str.replace(/[\u0080-\uffff]/g, function(ch) {
        var code = ch.charCodeAt(0).toString(16);
        while (code.length < 4) code = "0" + code;
        return "\\u" + code;
    });
};

var SPLICE_NEEDS_BRACKETS = jsp.array_to_hash([ "if", "while", "do", "for", "for-in", "with" ]);

function gen_code(ast, options) {
    options = defaults(options, {
        indent_start : 0,
        indent_level : 4,
        quote_keys   : false,
        space_colon  : false,
        beautify     : false,
        ascii_only   : false,
        inline_script: false
    });
    var beautify = !!options.beautify;
    var indentation = 0,
    newline = beautify ? "\n" : "",
    space = beautify ? " " : "";

    function encode_string(str) {
        var ret = make_string(str, options.ascii_only);
        if (options.inline_script)
            ret = ret.replace(/<\x2fscript([>\/\t\n\f\r ])/gi, "<\\/script$1");
        return ret;
    };

    function make_name(name) {
        name = name.toString();
        if (options.ascii_only)
            name = to_ascii(name);
        return name;
    };

    function indent(line) {
        if (line == null)
            line = "";
        if (beautify)
            line = repeat_string(" ", options.indent_start + indentation * options.indent_level) + line;
        return line;
    };

    function with_indent(cont, incr) {
        if (incr == null) incr = 1;
        indentation += incr;
        try { return cont.apply(null, slice(arguments, 1)); }
        finally { indentation -= incr; }
    };

    function last_char(str) {
        str = str.toString();
        var ch = str.charAt(str.length - 1);

        if (str.length > 1) {
            var previous = str.charAt(str.length - 2);
            if ((previous.charCodeAt(0) & 0xff00) == 0xd800) {
                ch = previous + ch;
            }
        }
        return ch;
    };

    function first_char(str) {
        str = str.toString();
        var ch = str.charAt(0);

        if ((ch.charCodeAt(0) & 0xff00) == 0xd800) {
            ch += str.charAt(1);
        }
        return ch;
    };

    function add_spaces(a) {
        if (beautify)
            return a.join(" ");
        var b = [];
        for (var i = 0; i < a.length; ++i) {
            var next = a[i + 1];
            b.push(a[i]);
            if (next &&
                ((is_identifier_char(last_char(a[i])) && (is_identifier_char(first_char(next))
                                                          || first_char(next) == "\\")) ||
                 (/[\+\-]$/.test(a[i].toString()) && /^[\+\-]/.test(next.toString()) ||
                 last_char(a[i]) == "/" && first_char(next) == "/"))) {
                b.push(" ");
            }
        }
        return b.join("");
    };

    function add_commas(a) {
        return a.join("," + space);
    };

    function parenthesize(expr) {
        var gen = make(expr);
        for (var i = 1; i < arguments.length; ++i) {
            var el = arguments[i];
            if ((el instanceof Function && el(expr)) || expr[0] == el)
                return "(" + gen + ")";
        }
        return gen;
    };

    function best_of(a) {
        if (a.length == 1) {
            return a[0];
        }
        if (a.length == 2) {
            var b = a[1];
            a = a[0];
            return a.length <= b.length ? a : b;
        }
        return best_of([ a[0], best_of(a.slice(1)) ]);
    };

    function needs_parens(expr) {
        if (expr[0] == "function" || expr[0] == "object") {
            // dot/call on a literal function requires the
            // function literal itself to be parenthesized
            // only if it's the first "thing" in a
            // statement.  This means that the parent is
            // "stat", but it could also be a "seq" and
            // we're the first in this "seq" and the
            // parent is "stat", and so on.  Messy stuff,
            // but it worths the trouble.
            var a = slice(w.stack()), self = a.pop(), p = a.pop();
            while (p) {
                if (p[0] == "stat") return true;
                if (((p[0] == "seq" || p[0] == "call" || p[0] == "dot" || p[0] == "sub" || p[0] == "conditional") && p[1] === self) ||
                    ((p[0] == "binary" || p[0] == "assign" || p[0] == "unary-postfix") && p[2] === self)) {
                    self = p;
                    p = a.pop();
                } else {
                    return false;
                }
            }
        }
        return !HOP(DOT_CALL_NO_PARENS, expr[0]);
    };

    function make_num(num) {
        var str = num.toString(10), a = [ str.replace(/^0\./, ".").replace('e+', 'e') ], m;
        if (Math.floor(num) === num) {
            if (num >= 0) {
                a.push("0x" + num.toString(16).toLowerCase(), // probably pointless
                       "0" + num.toString(8)); // same.
            } else {
                a.push("-0x" + (-num).toString(16).toLowerCase(), // probably pointless
                       "-0" + (-num).toString(8)); // same.
            }
            if ((m = /^(.*?)(0+)$/.exec(num))) {
                a.push(m[1] + "e" + m[2].length);
            }
        } else if ((m = /^0?\.(0+)(.*)$/.exec(num))) {
            a.push(m[2] + "e-" + (m[1].length + m[2].length),
                   str.substr(str.indexOf(".")));
        }
        return best_of(a);
    };

    var w = ast_walker();
    var make = w.walk;
    return w.with_walkers({
        "string": encode_string,
        "num": make_num,
        "name": make_name,
        "debugger": function(){ return "debugger;" },
        "toplevel": function(statements) {
            return make_block_statements(statements)
                .join(newline + newline);
        },
        "splice": function(statements) {
            var parent = w.parent();
            if (HOP(SPLICE_NEEDS_BRACKETS, parent)) {
                // we need block brackets in this case
                return make_block.apply(this, arguments);
            } else {
                return MAP(make_block_statements(statements, true),
                           function(line, i) {
                               // the first line is already indented
                               return i > 0 ? indent(line) : line;
                           }).join(newline);
            }
        },
        "block": make_block,
        "var": function(defs) {
            return "var " + add_commas(MAP(defs, make_1vardef)) + ";";
        },
        "const": function(defs) {
            return "const " + add_commas(MAP(defs, make_1vardef)) + ";";
        },
        "try": function(tr, ca, fi) {
            var out = [ "try", make_block(tr) ];
            if (ca) out.push("catch", "(" + ca[0] + ")", make_block(ca[1]));
            if (fi) out.push("finally", make_block(fi));
            return add_spaces(out);
        },
        "throw": function(expr) {
            return add_spaces([ "throw", make(expr) ]) + ";";
        },
        "new": function(ctor, args) {
            args = args.length > 0 ? "(" + add_commas(MAP(args, function(expr){
                return parenthesize(expr, "seq");
            })) + ")" : "";
            return add_spaces([ "new", parenthesize(ctor, "seq", "binary", "conditional", "assign", function(expr){
                var w = ast_walker(), has_call = {};
                try {
                    w.with_walkers({
                        "call": function() { throw has_call },
                        "function": function() { return this }
                    }, function(){
                        w.walk(expr);
                    });
                } catch(ex) {
                    if (ex === has_call)
                        return true;
                    throw ex;
                }
            }) + args ]);
        },
        "switch": function(expr, body) {
            return add_spaces([ "switch", "(" + make(expr) + ")", make_switch_block(body) ]);
        },
        "break": function(label) {
            var out = "break";
            if (label != null)
                out += " " + make_name(label);
            return out + ";";
        },
        "continue": function(label) {
            var out = "continue";
            if (label != null)
                out += " " + make_name(label);
            return out + ";";
        },
        "conditional": function(co, th, el) {
            return add_spaces([ parenthesize(co, "assign", "seq", "conditional"), "?",
                                parenthesize(th, "seq"), ":",
                                parenthesize(el, "seq") ]);
        },
        "assign": function(op, lvalue, rvalue) {
            if (op && op !== true) op += "=";
            else op = "=";
            return add_spaces([ make(lvalue), op, parenthesize(rvalue, "seq") ]);
        },
        "dot": function(expr) {
            var out = make(expr), i = 1;
            if (expr[0] == "num") {
                if (!/[a-f.]/i.test(out))
                    out += ".";
            } else if (expr[0] != "function" && needs_parens(expr))
                out = "(" + out + ")";
            while (i < arguments.length)
                out += "." + make_name(arguments[i++]);
            return out;
        },
        "call": function(func, args) {
            var f = make(func);
            // cannot simply test the first and/or the last characters in the genetic case,
            // because the called expression might look like e.g. `(x || y) && (u || v)`.
            var already_wrapped = (func[0] == "function" && f.charAt(0) == "(");
            if (!already_wrapped && needs_parens(func))
                f = "(" + f + ")";
            return f + "(" + add_commas(MAP(args, function(expr){
                return parenthesize(expr, "seq");
            })) + ")";
        },
        "function": make_function,
        "defun": make_function,
        "if": function(co, th, el) {
            var out = [ "if", "(" + make(co) + ")", el ? make_then(th) : make(th) ];
            if (el) {
                out.push("else", make(el));
            }
            return add_spaces(out);
        },
        "for": function(init, cond, step, block) {
            var out = [ "for" ];
            init = (init != null ? make(init) : "").replace(/;*\s*$/, ";" + space);
            cond = (cond != null ? make(cond) : "").replace(/;*\s*$/, ";" + space);
            step = (step != null ? make(step) : "").replace(/;*\s*$/, "");
            var args = init + cond + step;
            if (args == "; ; ") args = ";;";
            out.push("(" + args + ")", make(block));
            return add_spaces(out);
        },
        "for-in": function(vvar, key, hash, block) {
            debugger;
            return add_spaces([ "for", "(" +
                                (vvar ? make(vvar).replace(/;+$/, "") : make(key)),
                                "in",
                                make(hash) + ")", make(block) ]);
        },
        "while": function(condition, block) {
            return add_spaces([ "while", "(" + make(condition) + ")", make(block) ]);
        },
        "do": function(condition, block) {
            return add_spaces([ "do", make(block), "while", "(" + make(condition) + ")" ]) + ";";
        },
        "return": function(expr) {
            var out = [ "return" ];
            if (expr != null) out.push(make(expr));
            return add_spaces(out) + ";";
        },
        "binary": function(operator, lvalue, rvalue) {
            var left = make(lvalue), right = make(rvalue);
            // XXX: I'm pretty sure other cases will bite here.
            //      we need to be smarter.
            //      adding parens all the time is the safest bet.
            if (member(lvalue[0], [ "assign", "conditional", "seq" ]) ||
                lvalue[0] == "binary" && PRECEDENCE[operator] > PRECEDENCE[lvalue[1]] ||
                lvalue[0] == "function" && needs_parens(this)) {
                left = "(" + left + ")";
            }
            if (member(rvalue[0], [ "assign", "conditional", "seq" ]) ||
                rvalue[0] == "binary" && PRECEDENCE[operator] >= PRECEDENCE[rvalue[1]] &&
                !(rvalue[1] == operator && member(operator, [ "&&", "||", "*" ]))) {
                right = "(" + right + ")";
            }
            else if (!beautify && options.inline_script && (operator == "<" || operator == "<<")
                     && rvalue[0] == "regexp" && /^script/i.test(rvalue[1])) {
                right = " " + right;
            }
            return add_spaces([ left, operator, right ]);
        },
        "unary-prefix": function(operator, expr) {
            var val = make(expr);
            if (!(expr[0] == "num" || (expr[0] == "unary-prefix" && !HOP(OPERATORS, operator + expr[1])) || !needs_parens(expr)))
                val = "(" + val + ")";
            return operator + (jsp.is_alphanumeric_char(operator.charAt(0)) ? " " : "") + val;
        },
        "unary-postfix": function(operator, expr) {
            var val = make(expr);
            if (!(expr[0] == "num" || (expr[0] == "unary-postfix" && !HOP(OPERATORS, operator + expr[1])) || !needs_parens(expr)))
                val = "(" + val + ")";
            return val + operator;
        },
        "sub": function(expr, subscript) {
            var hash = make(expr);
            if (needs_parens(expr))
                hash = "(" + hash + ")";
            return hash + "[" + make(subscript) + "]";
        },
        "object": function(props) {
            var obj_needs_parens = needs_parens(this);
            if (props.length == 0)
                return obj_needs_parens ? "({})" : "{}";
            var out = "{" + newline + with_indent(function(){
                return MAP(props, function(p){
                    if (p.length == 3) {
                        // getter/setter.  The name is in p[0], the arg.list in p[1][2], the
                        // body in p[1][3] and type ("get" / "set") in p[2].
                        return indent(make_function(p[0], p[1][2], p[1][3], p[2], true));
                    }
                    var key = p[0], val = parenthesize(p[1], "seq");
                    if (options.quote_keys) {
                        key = encode_string(key);
                    } else if ((typeof key == "number" || !beautify && +key + "" == key)
                               && parseFloat(key) >= 0) {
                        key = make_num(+key);
                    } else if (!is_identifier(key)) {
                        key = encode_string(key);
                    }
                    return indent(add_spaces(beautify && options.space_colon
                                             ? [ key, ":", val ]
                                             : [ key + ":", val ]));
                }).join("," + newline);
            }) + newline + indent("}");
            return obj_needs_parens ? "(" + out + ")" : out;
        },
        "regexp": function(rx, mods) {
            if (options.ascii_only) rx = to_ascii(rx);
            return "/" + rx + "/" + mods;
        },
        "array": function(elements) {
            if (elements.length == 0) return "[]";
            return add_spaces([ "[", add_commas(MAP(elements, function(el, i){
                if (!beautify && el[0] == "atom" && el[1] == "undefined") return i === elements.length - 1 ? "," : "";
                return parenthesize(el, "seq");
            })), "]" ]);
        },
        "stat": function(stmt) {
            return stmt != null
                ? make(stmt).replace(/;*\s*$/, ";")
                : ";";
        },
        "seq": function() {
            return add_commas(MAP(slice(arguments), make));
        },
        "label": function(name, block) {
            return add_spaces([ make_name(name), ":", make(block) ]);
        },
        "with": function(expr, block) {
            return add_spaces([ "with", "(" + make(expr) + ")", make(block) ]);
        },
        "atom": function(name) {
            return make_name(name);
        },
        "directive": function(dir) {
            return make_string(dir) + ";";
        }
    }, function(){ return make(ast) });

    // The squeezer replaces "block"-s that contain only a single
    // statement with the statement itself; technically, the AST
    // is correct, but this can create problems when we output an
    // IF having an ELSE clause where the THEN clause ends in an
    // IF *without* an ELSE block (then the outer ELSE would refer
    // to the inner IF).  This function checks for this case and
    // adds the block brackets if needed.
    function make_then(th) {
        if (th == null) return ";";
        if (th[0] == "do") {
            // https://github.com/mishoo/UglifyJS/issues/#issue/57
            // IE croaks with "syntax error" on code like this:
            //     if (foo) do ... while(cond); else ...
            // we need block brackets around do/while
            return make_block([ th ]);
        }
        var b = th;
        while (true) {
            var type = b[0];
            if (type == "if") {
                if (!b[3])
                    // no else, we must add the block
                    return make([ "block", [ th ]]);
                b = b[3];
            }
            else if (type == "while" || type == "do") b = b[2];
            else if (type == "for" || type == "for-in") b = b[4];
            else break;
        }
        return make(th);
    };

    function make_function(name, args, body, keyword, no_parens) {
        var out = keyword || "function";
        if (name) {
            out += " " + make_name(name);
        }
        out += "(" + add_commas(MAP(args, make_name)) + ")";
        out = add_spaces([ out, make_block(body) ]);
        return (!no_parens && needs_parens(this)) ? "(" + out + ")" : out;
    };

    function must_has_semicolon(node) {
        switch (node[0]) {
          case "with":
          case "while":
            return empty(node[2]) || must_has_semicolon(node[2]);
          case "for":
          case "for-in":
            return empty(node[4]) || must_has_semicolon(node[4]);
          case "if":
            if (empty(node[2]) && !node[3]) return true; // `if' with empty `then' and no `else'
            if (node[3]) {
                if (empty(node[3])) return true; // `else' present but empty
                return must_has_semicolon(node[3]); // dive into the `else' branch
            }
            return must_has_semicolon(node[2]); // dive into the `then' branch
          case "directive":
            return true;
        }
    };

    function make_block_statements(statements, noindent) {
        for (var a = [], last = statements.length - 1, i = 0; i <= last; ++i) {
            var stat = statements[i];
            var code = make(stat);
            if (code != ";") {
                if (!beautify && i == last && !must_has_semicolon(stat)) {
                    code = code.replace(/;+\s*$/, "");
                }
                a.push(code);
            }
        }
        return noindent ? a : MAP(a, indent);
    };

    function make_switch_block(body) {
        var n = body.length;
        if (n == 0) return "{}";
        return "{" + newline + MAP(body, function(branch, i){
            var has_body = branch[1].length > 0, code = with_indent(function(){
                return indent(branch[0]
                              ? add_spaces([ "case", make(branch[0]) + ":" ])
                              : "default:");
            }, 0.5) + (has_body ? newline + with_indent(function(){
                return make_block_statements(branch[1]).join(newline);
            }) : "");
            if (!beautify && has_body && i < n - 1)
                code += ";";
            return code;
        }).join(newline) + newline + indent("}");
    };

    function make_block(statements) {
        if (!statements) return ";";
        if (statements.length == 0) return "{}";
        return "{" + newline + with_indent(function(){
            return make_block_statements(statements).join(newline);
        }) + newline + indent("}");
    };

    function make_1vardef(def) {
        var name = def[0], val = def[1];
        if (val != null)
            name = add_spaces([ make_name(name), "=", parenthesize(val, "seq") ]);
        return name;
    };

};

function split_lines(code, max_line_length) {
    var splits = [ 0 ];
    jsp.parse(function(){
        var next_token = jsp.tokenizer(code);
        var last_split = 0;
        var prev_token;
        function current_length(tok) {
            return tok.pos - last_split;
        };
        function split_here(tok) {
            last_split = tok.pos;
            splits.push(last_split);
        };
        function custom(){
            var tok = next_token.apply(this, arguments);
            out: {
                if (prev_token) {
                    if (prev_token.type == "keyword") break out;
                }
                if (current_length(tok) > max_line_length) {
                    switch (tok.type) {
                      case "keyword":
                      case "atom":
                      case "name":
                      case "punc":
                        split_here(tok);
                        break out;
                    }
                }
            }
            prev_token = tok;
            return tok;
        };
        custom.context = function() {
            return next_token.context.apply(this, arguments);
        };
        return custom;
    }());
    return splits.map(function(pos, i){
        return code.substring(pos, splits[i + 1] || code.length);
    }).join("\n");
};

/* -----[ Utilities ]----- */

function repeat_string(str, i) {
    if (i <= 0) return "";
    if (i == 1) return str;
    var d = repeat_string(str, i >> 1);
    d += d;
    if (i & 1) d += str;
    return d;
};

function defaults(args, defs) {
    var ret = {};
    if (args === true)
        args = {};
    for (var i in defs) if (HOP(defs, i)) {
        ret[i] = (args && HOP(args, i)) ? args[i] : defs[i];
    }
    return ret;
};

function is_identifier(name) {
    var emoji = /^\uD83C(?:\uDDE6\uD83C(?:\uDDEB|\uDDFD|\uDDF1|\uDDF8|\uDDE9|\uDDF4|\uDDEE|\uDDF6|\uDDEC|\uDDF7|\uDDF2|\uDDFC|\uDDE8|\uDDFA|\uDDF9|\uDDFF|\uDDEA)|\uDDE9\uD83C(?:\uDDFF|\uDDF0|\uDDEC|\uDDEF|\uDDF2|\uDDF4|\uDDEA)|\uDDE7\uD83C(?:\uDDF8|\uDDED|\uDDE9|\uDDE7|\uDDFE|\uDDEA|\uDDFF|\uDDEF|\uDDF2|\uDDF9|\uDDF4|\uDDE6|\uDDFC|\uDDFB|\uDDF7|\uDDF3|\uDDEC|\uDDEB|\uDDEE|\uDDF6|\uDDF1)|\uDDEE\uD83C(?:\uDDF4|\uDDE8|\uDDF8|\uDDF3|\uDDE9|\uDDF7|\uDDF6|\uDDEA|\uDDF2|\uDDF1|\uDDF9)|\uDDFB\uD83C(?:\uDDEC|\uDDE8|\uDDEE|\uDDFA|\uDDE6|\uDDEA|\uDDF3)|\uDDF0\uD83C(?:\uDDED|\uDDFE|\uDDF2|\uDDFF|\uDDEA|\uDDEE|\uDDFC|\uDDEC|\uDDF5|\uDDF7|\uDDF3)|\uDDE8\uD83C(?:\uDDF2|\uDDE6|\uDDFB|\uDDEB|\uDDF1|\uDDF3|\uDDFD|\uDDF5|\uDDE8|\uDDF4|\uDDEC|\uDDE9|\uDDF0|\uDDF7|\uDDEE|\uDDFA|\uDDFC|\uDDFE|\uDDFF|\uDDED)|\uDDEA\uD83C(?:\uDDE6|\uDDE8|\uDDEC|\uDDF7|\uDDEA|\uDDF9|\uDDFA|\uDDF8|\uDDED)|\uDDF9\uD83C(?:\uDDE9|\uDDEB|\uDDFC|\uDDEF|\uDDFF|\uDDED|\uDDF1|\uDDEC|\uDDF0|\uDDF4|\uDDF9|\uDDE6|\uDDF3|\uDDF7|\uDDF2|\uDDE8|\uDDFB)|\uDDED\uD83C(?:\uDDF7|\uDDF9|\uDDF2|\uDDF3|\uDDF0|\uDDFA)|\uDDF8\uD83C(?:\uDDFB|\uDDF2|\uDDF9|\uDDE6|\uDDF3|\uDDE8|\uDDF1|\uDDEC|\uDDFD|\uDDF0|\uDDEE|\uDDE7|\uDDF4|\uDDF8|\uDDED|\uDDE9|\uDDF7|\uDDEF|\uDDFF|\uDDEA|\uDDFE)|\uDDEC\uD83C(?:\uDDF6|\uDDEB|\uDDE6|\uDDF2|\uDDEA|\uDDED|\uDDEE|\uDDF7|\uDDF1|\uDDE9|\uDDF5|\uDDFA|\uDDF9|\uDDEC|\uDDF3|\uDDFC|\uDDFE|\uDDF8|\uDDE7)|\uDDEB\uD83C(?:\uDDF0|\uDDF4|\uDDEF|\uDDEE|\uDDF7|\uDDF2)|\uDDF5\uD83C(?:\uDDEB|\uDDF0|\uDDFC|\uDDF8|\uDDE6|\uDDEC|\uDDFE|\uDDEA|\uDDED|\uDDF3|\uDDF1|\uDDF9|\uDDF7|\uDDF2)|\uDDEF\uD83C(?:\uDDF2|\uDDF5|\uDDEA|\uDDF4)|\uDDFD\uD83C\uDDF0|\uDDF1\uD83C(?:\uDDE6|\uDDFB|\uDDE7|\uDDF8|\uDDF7|\uDDFE|\uDDEE|\uDDF9|\uDDFA|\uDDF0|\uDDE8)|\uDDF2\uD83C(?:\uDDF4|\uDDF0|\uDDEC|\uDDFC|\uDDFE|\uDDFB|\uDDF1|\uDDF9|\uDDED|\uDDF6|\uDDF7|\uDDFA|\uDDFD|\uDDE9|\uDDE8|\uDDF3|\uDDEA|\uDDF8|\uDDE6|\uDDFF|\uDDF2|\uDDF5|\uDDEB)|\uDDFE\uD83C(?:\uDDF9|\uDDEA)|\uDDF3\uD83C(?:\uDDE6|\uDDF7|\uDDF5|\uDDF1|\uDDE8|\uDDFF|\uDDEE|\uDDEA|\uDDEC|\uDDFA|\uDDEB|\uDDF4)|\uDDF4\uD83C\uDDF2|\uDDF6\uD83C\uDDE6|\uDDF7\uD83C(?:\uDDEA|\uDDF4|\uDDFA|\uDDFC|\uDDF8)|\uDDFC\uD83C(?:\uDDF8|\uDDEB)|\uDDFF\uD83C(?:\uDDE6|\uDDF2|\uDDFC)|\uDDFA\uD83C(?:\uDDEC|\uDDE6|\uDDF8|\uDDFE|\uDDF2|\uDDFF))|[\u231A\u231B\u23E9-\u23EC\u23F0\u23F3\u25FD\u25FE\u2614\u2615\u2648-\u2653\u267F\u2693\u26A1\u26AA\u26AB\u26BD\u26BE\u26C4\u26C5\u26CE\u26D4\u26EA\u26F2\u26F3\u26F5\u26FA\u26FD\u2705\u270A\u270B\u2728\u274C\u274E\u2753-\u2755\u2757\u2795-\u2797\u27B0\u27BF\u2B1B\u2B1C\u2B50\u2B55]|\uD83C[\uDC04\uDCCF\uDD8E\uDD91-\uDD9A\uDE01\uDE1A\uDE2F\uDE32-\uDE36\uDE38-\uDE3A\uDE50\uDE51\uDF00-\uDF20\uDF2D-\uDF35\uDF37-\uDF7C\uDF7E-\uDF93\uDFA0-\uDFCA\uDFCF-\uDFD3\uDFE0-\uDFF0\uDFF4\uDFF8-\uDFFF]|\uD83D[\uDC00-\uDC3E\uDC40\uDC42-\uDCFC\uDCFF-\uDD3D\uDD4B-\uDD4E\uDD50-\uDD67\uDD95\uDD96\uDDFB-\uDE4F\uDE80-\uDEC5\uDECC\uDED0\uDEEB\uDEEC]|\uD83E[\uDD10-\uDD18\uDD80-\uDD84\uDDC0]$/;
    var es6Identifier = /^(?!(?:do|if|in|for|let|new|try|var|case|else|enum|eval|null|this|true|void|with|await|break|catch|class|const|false|super|throw|while|yield|delete|export|import|public|return|static|switch|typeof|default|extends|finally|package|private|continue|debugger|function|arguments|interface|protected|implements|instanceof)$)(?:[\$A-Z_a-z\xAA\xB5\xBA\xC0-\xD6\xD8-\xF6\xF8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u037F\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u052F\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0-\u08B2\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0980\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u16EE-\u16F8\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191E\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2118-\u211D\u2124\u2126\u2128\u212A-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2160-\u2188\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u3005-\u3007\u3021-\u3029\u3031-\u3035\u3038-\u303C\u3041-\u3096\u309B-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA69D\uA6A0-\uA6EF\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA7AD\uA7B0\uA7B1\uA7F7-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uA9E0-\uA9E4\uA9E6-\uA9EF\uA9FA-\uA9FE\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA7E-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uAB30-\uAB5A\uAB5C-\uAB5F\uAB64\uAB65\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]|\uD800[\uDC00-\uDC0B\uDC0D-\uDC26\uDC28-\uDC3A\uDC3C\uDC3D\uDC3F-\uDC4D\uDC50-\uDC5D\uDC80-\uDCFA\uDD40-\uDD74\uDE80-\uDE9C\uDEA0-\uDED0\uDF00-\uDF1F\uDF30-\uDF4A\uDF50-\uDF75\uDF80-\uDF9D\uDFA0-\uDFC3\uDFC8-\uDFCF\uDFD1-\uDFD5]|\uD801[\uDC00-\uDC9D\uDD00-\uDD27\uDD30-\uDD63\uDE00-\uDF36\uDF40-\uDF55\uDF60-\uDF67]|\uD802[\uDC00-\uDC05\uDC08\uDC0A-\uDC35\uDC37\uDC38\uDC3C\uDC3F-\uDC55\uDC60-\uDC76\uDC80-\uDC9E\uDD00-\uDD15\uDD20-\uDD39\uDD80-\uDDB7\uDDBE\uDDBF\uDE00\uDE10-\uDE13\uDE15-\uDE17\uDE19-\uDE33\uDE60-\uDE7C\uDE80-\uDE9C\uDEC0-\uDEC7\uDEC9-\uDEE4\uDF00-\uDF35\uDF40-\uDF55\uDF60-\uDF72\uDF80-\uDF91]|\uD803[\uDC00-\uDC48]|\uD804[\uDC03-\uDC37\uDC83-\uDCAF\uDCD0-\uDCE8\uDD03-\uDD26\uDD50-\uDD72\uDD76\uDD83-\uDDB2\uDDC1-\uDDC4\uDDDA\uDE00-\uDE11\uDE13-\uDE2B\uDEB0-\uDEDE\uDF05-\uDF0C\uDF0F\uDF10\uDF13-\uDF28\uDF2A-\uDF30\uDF32\uDF33\uDF35-\uDF39\uDF3D\uDF5D-\uDF61]|\uD805[\uDC80-\uDCAF\uDCC4\uDCC5\uDCC7\uDD80-\uDDAE\uDE00-\uDE2F\uDE44\uDE80-\uDEAA]|\uD806[\uDCA0-\uDCDF\uDCFF\uDEC0-\uDEF8]|\uD808[\uDC00-\uDF98]|\uD809[\uDC00-\uDC6E]|[\uD80C\uD840-\uD868\uD86A-\uD86C][\uDC00-\uDFFF]|\uD80D[\uDC00-\uDC2E]|\uD81A[\uDC00-\uDE38\uDE40-\uDE5E\uDED0-\uDEED\uDF00-\uDF2F\uDF40-\uDF43\uDF63-\uDF77\uDF7D-\uDF8F]|\uD81B[\uDF00-\uDF44\uDF50\uDF93-\uDF9F]|\uD82C[\uDC00\uDC01]|\uD82F[\uDC00-\uDC6A\uDC70-\uDC7C\uDC80-\uDC88\uDC90-\uDC99]|\uD835[\uDC00-\uDC54\uDC56-\uDC9C\uDC9E\uDC9F\uDCA2\uDCA5\uDCA6\uDCA9-\uDCAC\uDCAE-\uDCB9\uDCBB\uDCBD-\uDCC3\uDCC5-\uDD05\uDD07-\uDD0A\uDD0D-\uDD14\uDD16-\uDD1C\uDD1E-\uDD39\uDD3B-\uDD3E\uDD40-\uDD44\uDD46\uDD4A-\uDD50\uDD52-\uDEA5\uDEA8-\uDEC0\uDEC2-\uDEDA\uDEDC-\uDEFA\uDEFC-\uDF14\uDF16-\uDF34\uDF36-\uDF4E\uDF50-\uDF6E\uDF70-\uDF88\uDF8A-\uDFA8\uDFAA-\uDFC2\uDFC4-\uDFCB]|\uD83A[\uDC00-\uDCC4]|\uD83B[\uDE00-\uDE03\uDE05-\uDE1F\uDE21\uDE22\uDE24\uDE27\uDE29-\uDE32\uDE34-\uDE37\uDE39\uDE3B\uDE42\uDE47\uDE49\uDE4B\uDE4D-\uDE4F\uDE51\uDE52\uDE54\uDE57\uDE59\uDE5B\uDE5D\uDE5F\uDE61\uDE62\uDE64\uDE67-\uDE6A\uDE6C-\uDE72\uDE74-\uDE77\uDE79-\uDE7C\uDE7E\uDE80-\uDE89\uDE8B-\uDE9B\uDEA1-\uDEA3\uDEA5-\uDEA9\uDEAB-\uDEBB]|\uD869[\uDC00-\uDED6\uDF00-\uDFFF]|\uD86D[\uDC00-\uDF34\uDF40-\uDFFF]|\uD86E[\uDC00-\uDC1D]|\uD87E[\uDC00-\uDE1D])(?:[\$0-9A-Z_a-z\xAA\xB5\xB7\xBA\xC0-\xD6\xD8-\xF6\xF8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0300-\u0374\u0376\u0377\u037A-\u037D\u037F\u0386-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u0483-\u0487\u048A-\u052F\u0531-\u0556\u0559\u0561-\u0587\u0591-\u05BD\u05BF\u05C1\u05C2\u05C4\u05C5\u05C7\u05D0-\u05EA\u05F0-\u05F2\u0610-\u061A\u0620-\u0669\u066E-\u06D3\u06D5-\u06DC\u06DF-\u06E8\u06EA-\u06FC\u06FF\u0710-\u074A\u074D-\u07B1\u07C0-\u07F5\u07FA\u0800-\u082D\u0840-\u085B\u08A0-\u08B2\u08E4-\u0963\u0966-\u096F\u0971-\u0983\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BC-\u09C4\u09C7\u09C8\u09CB-\u09CE\u09D7\u09DC\u09DD\u09DF-\u09E3\u09E6-\u09F1\u0A01-\u0A03\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A3C\u0A3E-\u0A42\u0A47\u0A48\u0A4B-\u0A4D\u0A51\u0A59-\u0A5C\u0A5E\u0A66-\u0A75\u0A81-\u0A83\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABC-\u0AC5\u0AC7-\u0AC9\u0ACB-\u0ACD\u0AD0\u0AE0-\u0AE3\u0AE6-\u0AEF\u0B01-\u0B03\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3C-\u0B44\u0B47\u0B48\u0B4B-\u0B4D\u0B56\u0B57\u0B5C\u0B5D\u0B5F-\u0B63\u0B66-\u0B6F\u0B71\u0B82\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BBE-\u0BC2\u0BC6-\u0BC8\u0BCA-\u0BCD\u0BD0\u0BD7\u0BE6-\u0BEF\u0C00-\u0C03\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C39\u0C3D-\u0C44\u0C46-\u0C48\u0C4A-\u0C4D\u0C55\u0C56\u0C58\u0C59\u0C60-\u0C63\u0C66-\u0C6F\u0C81-\u0C83\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBC-\u0CC4\u0CC6-\u0CC8\u0CCA-\u0CCD\u0CD5\u0CD6\u0CDE\u0CE0-\u0CE3\u0CE6-\u0CEF\u0CF1\u0CF2\u0D01-\u0D03\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D-\u0D44\u0D46-\u0D48\u0D4A-\u0D4E\u0D57\u0D60-\u0D63\u0D66-\u0D6F\u0D7A-\u0D7F\u0D82\u0D83\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0DCA\u0DCF-\u0DD4\u0DD6\u0DD8-\u0DDF\u0DE6-\u0DEF\u0DF2\u0DF3\u0E01-\u0E3A\u0E40-\u0E4E\u0E50-\u0E59\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB9\u0EBB-\u0EBD\u0EC0-\u0EC4\u0EC6\u0EC8-\u0ECD\u0ED0-\u0ED9\u0EDC-\u0EDF\u0F00\u0F18\u0F19\u0F20-\u0F29\u0F35\u0F37\u0F39\u0F3E-\u0F47\u0F49-\u0F6C\u0F71-\u0F84\u0F86-\u0F97\u0F99-\u0FBC\u0FC6\u1000-\u1049\u1050-\u109D\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u135D-\u135F\u1369-\u1371\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u16EE-\u16F8\u1700-\u170C\u170E-\u1714\u1720-\u1734\u1740-\u1753\u1760-\u176C\u176E-\u1770\u1772\u1773\u1780-\u17D3\u17D7\u17DC\u17DD\u17E0-\u17E9\u180B-\u180D\u1810-\u1819\u1820-\u1877\u1880-\u18AA\u18B0-\u18F5\u1900-\u191E\u1920-\u192B\u1930-\u193B\u1946-\u196D\u1970-\u1974\u1980-\u19AB\u19B0-\u19C9\u19D0-\u19DA\u1A00-\u1A1B\u1A20-\u1A5E\u1A60-\u1A7C\u1A7F-\u1A89\u1A90-\u1A99\u1AA7\u1AB0-\u1ABD\u1B00-\u1B4B\u1B50-\u1B59\u1B6B-\u1B73\u1B80-\u1BF3\u1C00-\u1C37\u1C40-\u1C49\u1C4D-\u1C7D\u1CD0-\u1CD2\u1CD4-\u1CF6\u1CF8\u1CF9\u1D00-\u1DF5\u1DFC-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u200C\u200D\u203F\u2040\u2054\u2071\u207F\u2090-\u209C\u20D0-\u20DC\u20E1\u20E5-\u20F0\u2102\u2107\u210A-\u2113\u2115\u2118-\u211D\u2124\u2126\u2128\u212A-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2160-\u2188\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D7F-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2DE0-\u2DFF\u3005-\u3007\u3021-\u302F\u3031-\u3035\u3038-\u303C\u3041-\u3096\u3099-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA62B\uA640-\uA66F\uA674-\uA67D\uA67F-\uA69D\uA69F-\uA6F1\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA7AD\uA7B0\uA7B1\uA7F7-\uA827\uA840-\uA873\uA880-\uA8C4\uA8D0-\uA8D9\uA8E0-\uA8F7\uA8FB\uA900-\uA92D\uA930-\uA953\uA960-\uA97C\uA980-\uA9C0\uA9CF-\uA9D9\uA9E0-\uA9FE\uAA00-\uAA36\uAA40-\uAA4D\uAA50-\uAA59\uAA60-\uAA76\uAA7A-\uAAC2\uAADB-\uAADD\uAAE0-\uAAEF\uAAF2-\uAAF6\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uAB30-\uAB5A\uAB5C-\uAB5F\uAB64\uAB65\uABC0-\uABEA\uABEC\uABED\uABF0-\uABF9\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE00-\uFE0F\uFE20-\uFE2D\uFE33\uFE34\uFE4D-\uFE4F\uFE70-\uFE74\uFE76-\uFEFC\uFF10-\uFF19\uFF21-\uFF3A\uFF3F\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]|\uD800[\uDC00-\uDC0B\uDC0D-\uDC26\uDC28-\uDC3A\uDC3C\uDC3D\uDC3F-\uDC4D\uDC50-\uDC5D\uDC80-\uDCFA\uDD40-\uDD74\uDDFD\uDE80-\uDE9C\uDEA0-\uDED0\uDEE0\uDF00-\uDF1F\uDF30-\uDF4A\uDF50-\uDF7A\uDF80-\uDF9D\uDFA0-\uDFC3\uDFC8-\uDFCF\uDFD1-\uDFD5]|\uD801[\uDC00-\uDC9D\uDCA0-\uDCA9\uDD00-\uDD27\uDD30-\uDD63\uDE00-\uDF36\uDF40-\uDF55\uDF60-\uDF67]|\uD802[\uDC00-\uDC05\uDC08\uDC0A-\uDC35\uDC37\uDC38\uDC3C\uDC3F-\uDC55\uDC60-\uDC76\uDC80-\uDC9E\uDD00-\uDD15\uDD20-\uDD39\uDD80-\uDDB7\uDDBE\uDDBF\uDE00-\uDE03\uDE05\uDE06\uDE0C-\uDE13\uDE15-\uDE17\uDE19-\uDE33\uDE38-\uDE3A\uDE3F\uDE60-\uDE7C\uDE80-\uDE9C\uDEC0-\uDEC7\uDEC9-\uDEE6\uDF00-\uDF35\uDF40-\uDF55\uDF60-\uDF72\uDF80-\uDF91]|\uD803[\uDC00-\uDC48]|\uD804[\uDC00-\uDC46\uDC66-\uDC6F\uDC7F-\uDCBA\uDCD0-\uDCE8\uDCF0-\uDCF9\uDD00-\uDD34\uDD36-\uDD3F\uDD50-\uDD73\uDD76\uDD80-\uDDC4\uDDD0-\uDDDA\uDE00-\uDE11\uDE13-\uDE37\uDEB0-\uDEEA\uDEF0-\uDEF9\uDF01-\uDF03\uDF05-\uDF0C\uDF0F\uDF10\uDF13-\uDF28\uDF2A-\uDF30\uDF32\uDF33\uDF35-\uDF39\uDF3C-\uDF44\uDF47\uDF48\uDF4B-\uDF4D\uDF57\uDF5D-\uDF63\uDF66-\uDF6C\uDF70-\uDF74]|\uD805[\uDC80-\uDCC5\uDCC7\uDCD0-\uDCD9\uDD80-\uDDB5\uDDB8-\uDDC0\uDE00-\uDE40\uDE44\uDE50-\uDE59\uDE80-\uDEB7\uDEC0-\uDEC9]|\uD806[\uDCA0-\uDCE9\uDCFF\uDEC0-\uDEF8]|\uD808[\uDC00-\uDF98]|\uD809[\uDC00-\uDC6E]|[\uD80C\uD840-\uD868\uD86A-\uD86C][\uDC00-\uDFFF]|\uD80D[\uDC00-\uDC2E]|\uD81A[\uDC00-\uDE38\uDE40-\uDE5E\uDE60-\uDE69\uDED0-\uDEED\uDEF0-\uDEF4\uDF00-\uDF36\uDF40-\uDF43\uDF50-\uDF59\uDF63-\uDF77\uDF7D-\uDF8F]|\uD81B[\uDF00-\uDF44\uDF50-\uDF7E\uDF8F-\uDF9F]|\uD82C[\uDC00\uDC01]|\uD82F[\uDC00-\uDC6A\uDC70-\uDC7C\uDC80-\uDC88\uDC90-\uDC99\uDC9D\uDC9E]|\uD834[\uDD65-\uDD69\uDD6D-\uDD72\uDD7B-\uDD82\uDD85-\uDD8B\uDDAA-\uDDAD\uDE42-\uDE44]|\uD835[\uDC00-\uDC54\uDC56-\uDC9C\uDC9E\uDC9F\uDCA2\uDCA5\uDCA6\uDCA9-\uDCAC\uDCAE-\uDCB9\uDCBB\uDCBD-\uDCC3\uDCC5-\uDD05\uDD07-\uDD0A\uDD0D-\uDD14\uDD16-\uDD1C\uDD1E-\uDD39\uDD3B-\uDD3E\uDD40-\uDD44\uDD46\uDD4A-\uDD50\uDD52-\uDEA5\uDEA8-\uDEC0\uDEC2-\uDEDA\uDEDC-\uDEFA\uDEFC-\uDF14\uDF16-\uDF34\uDF36-\uDF4E\uDF50-\uDF6E\uDF70-\uDF88\uDF8A-\uDFA8\uDFAA-\uDFC2\uDFC4-\uDFCB\uDFCE-\uDFFF]|\uD83A[\uDC00-\uDCC4\uDCD0-\uDCD6]|\uD83B[\uDE00-\uDE03\uDE05-\uDE1F\uDE21\uDE22\uDE24\uDE27\uDE29-\uDE32\uDE34-\uDE37\uDE39\uDE3B\uDE42\uDE47\uDE49\uDE4B\uDE4D-\uDE4F\uDE51\uDE52\uDE54\uDE57\uDE59\uDE5B\uDE5D\uDE5F\uDE61\uDE62\uDE64\uDE67-\uDE6A\uDE6C-\uDE72\uDE74-\uDE77\uDE79-\uDE7C\uDE7E\uDE80-\uDE89\uDE8B-\uDE9B\uDEA1-\uDEA3\uDEA5-\uDEA9\uDEAB-\uDEBB]|\uD869[\uDC00-\uDED6\uDF00-\uDFFF]|\uD86D[\uDC00-\uDF34\uDF40-\uDFFF]|\uD86E[\uDC00-\uDC1D]|\uD87E[\uDC00-\uDE1D]|\uDB40[\uDD00-\uDDEF])*$/;
    return (/^[a-z_$][a-z0-9_$]*$/i.test(name) || es6Identifier.test(name) || emoji.test(name))
        && name != "this"
        && !HOP(jsp.KEYWORDS_ATOM, name)
        && !HOP(jsp.RESERVED_WORDS, name)
        && !HOP(jsp.KEYWORDS, name);
};

function HOP(obj, prop) {
    return Object.prototype.hasOwnProperty.call(obj, prop);
};

// some utilities

var MAP;

(function(){
    MAP = function(a, f, o) {
        var ret = [], top = [], i;
        function doit() {
            var val = f.call(o, a[i], i);
            if (val instanceof AtTop) {
                val = val.v;
                if (val instanceof Splice) {
                    top.push.apply(top, val.v);
                } else {
                    top.push(val);
                }
            }
            else if (val != skip) {
                if (val instanceof Splice) {
                    ret.push.apply(ret, val.v);
                } else {
                    ret.push(val);
                }
            }
        };
        if (a instanceof Array) for (i = 0; i < a.length; ++i) doit();
        else for (i in a) if (HOP(a, i)) doit();
        return top.concat(ret);
    };
    MAP.at_top = function(val) { return new AtTop(val) };
    MAP.splice = function(val) { return new Splice(val) };
    var skip = MAP.skip = {};
    function AtTop(val) { this.v = val };
    function Splice(val) { this.v = val };
})();

/* -----[ Exports ]----- */

exports.ast_walker = ast_walker;
exports.ast_mangle = ast_mangle;
exports.ast_squeeze = ast_squeeze;
exports.ast_lift_variables = ast_lift_variables;
exports.gen_code = gen_code;
exports.ast_add_scope = ast_add_scope;
exports.set_logger = function(logger) { warn = logger };
exports.make_string = make_string;
exports.split_lines = split_lines;
exports.MAP = MAP;

// keep this last!
exports.ast_squeeze_more = require("./squeeze-more").ast_squeeze_more;

// Local variables:
// js-indent-level: 4
// End:
