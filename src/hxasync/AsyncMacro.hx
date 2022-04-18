package hxasync;

import haxe.ds.ReadOnlyArray;
#if macro
import haxe.macro.Context;
import haxe.macro.Compiler;
import haxe.macro.Expr;
import sys.io.File;

using haxe.macro.TypeTools;
using haxe.macro.ComplexTypeTools;
using haxe.macro.ExprTools;
using hxasync.AsyncMacroUtils;

abstract ReadOnlyFunction(Function) from Function {
    public var args(get, never):ReadOnlyArray<FunctionArg>;
	public var ret(get, never):Null<ComplexType>;
    public var expr(get, never):ReadOnlyExpr;
	public var params(get, never):ReadOnlyArray<TypeParamDecl>;
    function get_args() {
        return this.args;
    }

    function get_ret() {
        return this.ret;
    }

    function get_expr() {
        return this.expr;
    }

    function get_params() {
        return this.params;
    }

    public function underlying():Function {
        return this;
    }
}

abstract ReadOnlyExpr(Expr) from Expr {

    public var expr(get, never):ExprDef;
    public var pos(get, never):Position;

    function get_expr() {
        return this.expr;
    }

    function get_pos() {
        return this.pos;
    }

    public function underlying():Expr {
        return this;
    }
}
class AsyncMacro {
  public static var callbackRegistered: Bool = false;
  public static var notificationSent: Bool = false;
  public static var asyncPlaceholder = "%asyncPlaceholder%";
  public static var noReturnPlaceholder = "%noReturnPlaceholder%";

  macro public static function build(): Array<Field> {
    var targetName = Context.definedValue("target.name");
    if (isSync()) {
      return null;
    }
    if (!["python", "js"].contains(targetName)) {
      return null;
    }
    registerFinishCallback();
    var fields = Context.getBuildFields();
    final newFields:Array<Field> = [];
    for (field in fields) {
      var meta = field.meta;
      var asyncContext = false;
      for (data in meta) {
        if (data.name == "async") {
          asyncContext = true;
          break;
        }
      }
      switch field.kind {
        case FFun(f):
          f = (asyncContext) ? transformToAsync(f) : f;
          final newF:Function = {
              args: f.args,
              ret: f.ret,
              expr: handleAny(f.expr, asyncContext),
              params: f.params
          }
         final newField:Field = {
            name: field.name,
            doc: field.doc,
            access: field.access,
            kind: FFun(newF),
            pos: field.pos,
            meta: field.meta
          };
          newFields.push(newField);
        default:
          if (asyncContext) {
            Context.error("async can be applied only to a function field type", field.pos);
          }
          newFields.push(field);
      }
    }
    return newFields;
  }

  static function makeAsyncable(pathFilter: String) {
    Compiler.addGlobalMetadata(pathFilter, "@:build(hxasync.AsyncMacro.build())");
  }

  public static function isSync(): Bool {
    if (Context.definedValue("sync") == "1") {
      if (!notificationSent) {
        trace("\"sync\" flag is set. Ignoring async/await keywords");
      }
      notificationSent = true;
      return true;
    }
    return false;
  }

  public static inline function handleEMeta(
      expr: ReadOnlyExpr,
      isAsyncContext: Bool,
      addParenthesis: Bool = false
  ):Expr {
    return switch expr.expr {
      case EMeta(s, e):
        if (s.name == "await") {
          if (!isAsyncContext) {
            Context.error("await allowed only inside async function", e.pos);
          }
          transformToAwait(expr, addParenthesis);
        } else if (s.name == "async") {
          switch e.expr {
            case EFunction(kind, f):
              final newF = transformToAsync(f);
              handleEFunction(newF, kind, true, e.pos);
            default:
              Context.error("async only allowed to be used with functions", e.pos);
          }
        } else {
          handleAny(e, isAsyncContext);
        }
      default:
        Context.error("Expr is not EMeta", expr.pos);
    }
  }

  public static function handleAny(expr: ReadOnlyExpr, isAsyncContext: Bool):Expr {
    if (expr == null) {
      Context.fatalError("expr should never be null", Context.currentPos());
    }
    final newExprDef:ExprDef = switch expr.expr {
      case EReturn(e):
        if (e == null) {
          expr.expr;
        } else {
          EReturn(handleAny(e, isAsyncContext));
        }
      case EMeta(s, e):
        // FIXME: this may not be right
        handleEMeta(expr, isAsyncContext).expr;
      case EBlock(exprs):
        final newExprs = exprs.map(expr -> handleAny(expr, isAsyncContext));
        EBlock(newExprs);
      case ECall(e, params):
        final newE = handleAny(e, isAsyncContext);
        final newParams = params.map(param -> handleAny(param, isAsyncContext));
        ECall(e, newParams);
      case EConst(s):
        expr.expr;
      case EField(e, field):
        EField(handleAny(e, isAsyncContext), field);
      case EVars(vars):
        final newVars = vars.map(variable ->
            if (variable.expr != null) {
              {
                name: variable.name,
                type: variable.type,
                expr: handleAny(variable.expr, isAsyncContext),
                isFinal: variable.isFinal,
                meta: variable.meta
              }
            } else {
              variable;
            }
        );
        EVars(newVars);
      case EFunction(kind, f):
        handleEFunction(f, kind, isAsyncContext, expr.pos).expr;
      case EObjectDecl(fields):
        final newFields = fields.map(field -> {
          field: field.field,
          expr: handleAny(field.expr, isAsyncContext),
          quotes: field.quotes
        });
        EObjectDecl(newFields);
      case EParenthesis(e):
        final newExpr = switch e.expr {
          case EMeta(s, expr):
            handleEMeta(e, isAsyncContext, true);
          default:
            handleAny(e, isAsyncContext);
        }
        EParenthesis(newExpr);
      case ECheckType(e, t):
        ECheckType(handleAny(e, isAsyncContext), t);
      case EIf(econd, eif, eelse):
        EIf(
          handleAny(econd, isAsyncContext),
          handleAny(eif, isAsyncContext),
          eelse != null ? handleAny(eelse, isAsyncContext) : null
        );
      case EBinop(op, e1, e2):
        EBinop(
          op,
          handleAny(e1, isAsyncContext),
          handleAny(e2, isAsyncContext)
        );
      case EThrow(e):
        EThrow(handleAny(e, isAsyncContext));
      case ENew(t, params):
        final newParams = params.map(param -> handleAny(param, isAsyncContext));
        ENew(t, newParams);
      case EArrayDecl(values):
        final newValues = values.map(val -> handleAny(val, isAsyncContext));
        EArrayDecl(newValues);
      case EFor(it, expr):
        EFor(
          handleAny(it, isAsyncContext),
          handleAny(expr, isAsyncContext)
        );
      case EArray(e1, e2):
        EArray(
          handleAny(e1, isAsyncContext),
          handleAny(e2, isAsyncContext)
        );
      case EUnop(op, postFix, e):
        EUnop(op, postFix, handleAny(e, isAsyncContext));
      case ESwitch(e, cases, edef):
        final newCases:Array<Case> = cases.map(cs -> {
          // TODO: do we need to worry about adding async/await into value or guard statements?
          values: cs.values,
          guard: cs.guard,
          expr: cs.expr != null ? handleAny(cs.expr, isAsyncContext) : null
        });
        ESwitch(
          handleAny(e, isAsyncContext),
          newCases,
          edef != null ? handleAny(edef, isAsyncContext) : null
        );
      case ECast(e, t):
        ECast(handleAny(e, isAsyncContext), t);
      case EContinue:
        expr.expr;
      case ETernary(econd, eif, eelse):
        ETernary(
          handleAny(econd, isAsyncContext),
          handleAny(eif, isAsyncContext),
          handleAny(eelse, isAsyncContext)
        );
      case EUntyped(e):
        EUntyped(handleAny(e, isAsyncContext));
      case ETry(e, catches):
        final newE = handleAny(e, isAsyncContext);
        final newCatches = catches.map(ctch -> {
          name: ctch.name,
          type: ctch.type,
          expr: handleAny(ctch.expr, isAsyncContext)
        });
        ETry(newE, newCatches);
      case EWhile(econd, e, normalWhile):
        EWhile(
          handleAny(econd, isAsyncContext),
          handleAny(e, isAsyncContext),
          normalWhile
        );
      case EBreak:
        expr.expr;
      case null:
        expr.expr;
      case other:
        Context.error('Unexpected expression ${other}', expr.pos);
        null;
    }

    final newExpr = {
      pos: expr.pos,
      expr: newExprDef
    }
    return newExpr;
  }

  public static function handleEFunction(
      fun: Function,
      kind: FunctionKind,
      isAsyncContext: Bool,
      pos: Position
  ):Expr {
    if (isAsyncContext) {
      switch kind {
        case FNamed(name, inlined):
          if (inlined) {
            if (fun.expr != null) {
              Context.error("Inline function can not be async", fun.expr.pos);
            }
            Context.error("Inline function can not be async", pos);
          }
        default:
          null;
      }
    }
    return handleAny(fun.expr, isAsyncContext);
  }

  public static function makeJSAsyncFunctions(content: String): String {
    var regex = new EReg('${asyncPlaceholder};\\s*', "gm");
    // split code by placeholder first (and remove extra newline to keep a code pretty)
    var codeParts = regex.split(content);
    // -1 because we don't need to do any parsing to the last splitted result
    for (codeIndex in 0...(codeParts.length - 1)) {
      var codePart = codeParts[codeIndex];
      var splitPattern = "\n";
      var codeSubparts = (new EReg(splitPattern, "gm")).split(codePart);

      var functionRegex = new EReg("((function|\\w*)?\\s*\\([^()]*\\)\\s*\\{)", "");
      // From the regex point of view, expression
      // if(a == null) {
      // does not differ from function
      // someFunction(a == null) {
      // that's why I decided to look from the bottom-up to the first opening bracket without pair:
      // let funcWithDefaults = function(a) {
      //   if(a == null) {
      //     a = "asd";
      //   }
      // match it against function regex and add `async` keyword there
      // counter is to maintan count of open and closed brackets
      var counter = 0;
      for (subcodeIndex in 0...codeSubparts.length) {
        var line = codeSubparts[
          codeSubparts.length - subcodeIndex - 1
        ];
        counter = counter + (AsyncMacroUtils.count(line, "}") - AsyncMacroUtils.count(line, "{"));
        if (counter < 0) {
          if (functionRegex.match(line)) {
            codeSubparts[
              codeSubparts.length - subcodeIndex - 1
            ] = functionRegex.replace(line, "async $1");
            codeParts[codeIndex] = codeSubparts.join(splitPattern);
            break;
          }
        }
      }
    }
    return codeParts.join("");
  }

  public static function deleteJSEmptyReturn(content: String): String {
    var emptyReturnRegex = new EReg('\\s*return ${AsyncMacro.noReturnPlaceholder};', "gm");
    return emptyReturnRegex.replace(content, "");
  }

  public static function fixJSOutput(content: String): String {
    content = makeJSAsyncFunctions(content);
    content = deleteJSEmptyReturn(content);
    return content;
  }

  public static function makePythonAsyncFunctions(content: String): String {
    var regex = new EReg('${asyncPlaceholder}\\s*', "gm");
    // split code by placeholder first (and remove extra newline to keep a code pretty)
    var codeParts = regex.split(content);
    // -1 because we don't need to do any parsing to the last splitted result
    for (codeIndex in 0...(codeParts.length - 1)) {
      var codePart = codeParts[codeIndex];
      // split evry part by lines and iterate from the last to first
      var splitPattern = "\n";
      var codeSubparts = (new EReg(splitPattern, "gm")).split(codePart);
      var functionRegex = new EReg("(def .*?\\(.*?\\):)", "");
      for (subcodeIndex in 0...codeSubparts.length) {
        var line = codeSubparts[
          codeSubparts.length - subcodeIndex - 1
        ];
        if (functionRegex.match(line)) {
          codeSubparts[
            codeSubparts.length - subcodeIndex - 1
          ] = functionRegex.replace(line, "async $1");
          codeParts[codeIndex] = codeSubparts.join(splitPattern);
          break;
        }
      }
    }
    return codeParts.join("");
  }

  public static function deletePythonEmptyReturn(content: String): String {
    var emptyReturnRegex = new EReg('\\s*return ${AsyncMacro.noReturnPlaceholder}', "gm");
    return emptyReturnRegex.replace(content, "");
  }

  public static function fixPythonOutput(content: String): String {
    content = makePythonAsyncFunctions(content);
    content = deletePythonEmptyReturn(content);
    return content;
  }

  public static function onFinishCallback() {
    var sourceCodePath = Compiler.getOutput();
    var target = Context.definedValue("target.name");
    var regex: EReg;
    var sourceCode = File.getContent(sourceCodePath);
    if (target == "js") {
      sourceCode = AsyncMacro.fixJSOutput(sourceCode);
    } else if (target == "python") {
      sourceCode = AsyncMacro.fixPythonOutput(sourceCode);
    }
    File.saveContent(sourceCodePath, sourceCode);
  }

  public static function registerFinishCallback() {
    if (callbackRegistered) {
      return;
    }
    callbackRegistered = true;
    Context.onAfterGenerate(onFinishCallback);
  }

  public static function getModifiedPlatformFunctionBody(e: ReadOnlyExpr):Expr {
    return switch Context.definedValue("target.name") {
      case "js":
        macro @:pos(e.pos) {
          std.js.Syntax.code("%asyncPlaceholder%");
          ${e.underlying()};
        };
      case "python":
        macro @:pos(e.pos) {
          std.python.Syntax.code("%asyncPlaceholder%");
          ${e.underlying()};
        };
      default:
        e.underlying();
    }
  }

  private static function getPythonEmptyReturn(pos: Position): Expr {
    return {
      expr: EReturn(
        macro @:pos(pos) return (std.python.Syntax.code("%noReturnPlaceholder%"))
      ),
      pos: pos
    };
  }

  private static function getJSEmptyReturn(pos: Position): Expr {
    return {
      expr: EReturn(
        macro @:pos(pos) return (std.js.Syntax.code("%noReturnPlaceholder%"))
      ),
      pos: pos
    };
  }

  public static function getEmptyReturn(expr: ReadOnlyExpr): ReadOnlyExpr {
    return switch Context.definedValue("target.name") {
      case "js":
        getJSEmptyReturn(expr.pos);
      case "python":
        getPythonEmptyReturn(expr.pos);
      case other:
        Context.error('Unsupported target ${other}', expr.pos);
    }
  }

  /*
  public static function makeExplicitReturn(expr: ReadOnlyExpr):Expr {
    switch expr.expr {
      case EBlock(outerExprs):
        var lastExpr = outerExprs[outerExprs.length - 1];
        if (lastExpr == null) {
          return {
            pos: expr.pos,
            expr: EBlock([getEmptyReturn(expr).underlying()])
          }
        }
        var newLastExpr = makeExplicitReturn(lastExpr);
        return {
          pos: expr.pos,
          expr: EBlock([
            for (expr in outerExprs) {
              if (expr == lastExpr) {
                newLastExpr;
              } else {
                expr;
              }
            }
          ])
        };

      case EReturn(e):
        return expr.underlying();
      case EMeta(s, e):
            if (s.name != ":implicitReturn") {
          exprs.push(getEmptyReturn(lastFunctionExpr));
            }
      default:
        exprs.push(getEmptyReturn(lastFunctionExpr));
    }
          case EMeta(s, e):
            switch e.expr {
              case EReturn(e):
                switch e.expr {
                  case EBlock(exprs):
                    var lastFunctionExpr = exprs[exprs.length - 1];
                    exprs.push(getEmptyReturn(lastFunctionExpr));
                  default:
                    null;
                }
              default:
                null;
            }
          default:
            null;
        }
      default:
        null;
    }
  }*/

  public static function makeExplicitReturn(expr:ReadOnlyExpr):Expr {
    return switch expr.expr {
      case EBlock(outerExprs):
        var lastExpr = outerExprs[outerExprs.length - 1];
        switch lastExpr.expr {
          case EBlock(innerExprs):
            var lastFunctionExpr = innerExprs[innerExprs.length - 1];
            if (lastFunctionExpr == null) {
              final newInnerExprs = innerExprs.copy();
              newInnerExprs.push(getEmptyReturn(lastExpr).underlying());
              final newLastExpr = {
                pos: lastExpr.pos,
                expr: EBlock(newInnerExprs)
              }
              return {
                pos: expr.pos,
                expr: EBlock([
                  for (expr in outerExprs) {
                    if (expr == lastExpr) {
                      newLastExpr;
                    } else {
                      expr;
                    }
                  }
                ])
              }
            }
            switch lastFunctionExpr.expr {
              case EReturn(e):
                return expr.underlying();
              //case EMeta(s, e):
               // exprs.push(getEmptyReturn(lastFunctionExpr));
               // default case
              default:
                final newInnerExprs = innerExprs.copy();
                newInnerExprs.push(getEmptyReturn(lastFunctionExpr).underlying());
                final newLastExpr = {
                  pos: lastExpr.pos,
                  expr: EBlock(newInnerExprs)
                }
                return {
                  pos: expr.pos,
                  expr: EBlock([
                    for (expr in outerExprs) {
                      if (expr == lastExpr) {
                        newLastExpr;
                      } else {
                        expr;
                      }
                    }
                  ])
                }
            }
          case EMeta(s, e):
            if (s.name != ":implicitReturn") {
              expr.underlying();
            }
            switch e.expr {
              case EReturn(e):
                switch e.expr {
                  case EBlock(returnExprs):
                    var lastReturnExpr = returnExprs[returnExprs.length - 1];
                    final newReturnExprs = returnExprs.copy();
                    newReturnExprs.push(getEmptyReturn(lastReturnExpr).underlying());
                    final newLastExpr = {
                      pos: lastExpr.pos,
                      expr: EBlock(newReturnExprs)
                    }
                    return {
                      pos: expr.pos,
                      expr: EBlock([
                        for (expr in outerExprs) {
                          if (expr == lastExpr) {
                            newLastExpr;
                          } else {
                            expr;
                          }
                        }
                      ])
                }
                  default:
                    expr.underlying();
                }
              default:
                expr.underlying();
            }
          default:
            expr.underlying();
        }
      default:
        expr.underlying();
    }
  }

  public static function inferReturnType(fun: ReadOnlyFunction): Null<ComplexType> {
    if (fun.ret != null) {
      return fun.ret;
    }
    var complexType = try {
      var typed = Context.typeExpr({expr: EFunction(null, fun.underlying()), pos: fun.expr.pos});
      typed.t.followWithAbstracts().toComplexType();
    }
    catch (e) {
      null;
    };

    return switch complexType {
      case TFunction(args, ret):
        ret;
      default:
        null;
    }
  }

  public static function getModifiedFunctionReturnType(fun: ReadOnlyFunction) {
    var returnType = inferReturnType(fun);
    return switch returnType {
      case TPath({name: "StdTypes", sub: "Void"}):
        macro
      : hxasync.Abstracts.Awaitable<hxasync.Abstracts.NoReturn>;
      case TPath(p):
        macro
      : hxasync.Abstracts.Awaitable<$returnType>;
      case null:
        null; // TODO: fix. Temporary fallback solution for cases when we failed to infer return type
      case TAnonymous(fields):
        macro
      : hxasync.Abstracts.Awaitable<$returnType>;
      default:
        trace('Unexpected return type: ${returnType}');
        trace(fun.expr.pos);
        macro
      : hxasync.Abstracts.Awaitable<$returnType>;
    }
  }

  /**
   * Modifies function body (by adding asyncPlaceholder) and (in future) changes return type from T to Promise<T>
   * @param {Function} fun -- Function to modify
   */
  public static function transformToAsync(fun: ReadOnlyFunction):Function {
    final newFun: Function = {
        args: fun.args != null ? fun.args.copy() : null,
        ret: fun.ret,
        expr: fun.expr != null ? cast fun.expr : null,
        params: fun.params != null ? fun.params.copy() : null,
    }
    if (Context.definedValue("inferTypes") == "1") {
      // Unstable feature
      newFun.ret = getModifiedFunctionReturnType(fun);
    }
    final newExpr = getModifiedPlatformFunctionBody(fun.expr);
    newFun.expr = makeExplicitReturn(newExpr);
    return newFun;
  }

  public static function processAwaitedFuncArgs(expr: ReadOnlyExpr):Expr {
    return switch expr.expr {
      case ECall(e, params):
        final newE = handleAny(e, true);
        final newParams = [];
        for (param in params) {
            newParams.push(handleAny(param, false));
        }
        return {
            pos: expr.pos,
            expr: ECall(newE, newParams)
        }
      default:
        expr.underlying();
    }
  }

  public static function transformToAwait(e: ReadOnlyExpr, addParenthesis: Bool):Expr {
    return switch (e.expr) {
      case EMeta(s, metaE):
        final newMetaE = processAwaitedFuncArgs(metaE);
        if (addParenthesis) {
          (macro hxasync.AsyncMacroUtils.awaitWithParenthesis(${newMetaE}));
        } else {
          (macro hxasync.AsyncMacroUtils.await(${newMetaE}));
        }
      default:
        Context.error("Invalid expression", e.pos);
    }
  }
}
#end
