#!/usr/bin/env python

from __future__ import with_statement

import os.path
import ast
from contextlib import contextmanager

class scala(object):
    def __init__(self, children = ()):
        self.children = children

class scalaExpr(scala):
    def __init__(self, children = (), prec = 0, assoc = 0):
        scala.__init__(self, children = children)
        self.prec = prec
        self.assoc = assoc

    def tilts(self):
        return tuple(0 for t in self.tilts())

    def precs(self):
        return tuple(self.prec for t in self.tilts())

    def kids_shown(self):
        tilts = self.tilts()
        precs = self.precs()
        return tuple((lambda: kid.show(prec = self.prec, assoc = self.assoc, tilt = tilt)) for (kid, tilt) in zip(self.children, tilts))

    def show(self, prec = 0, assoc = 0, tilt = 0):
        s = self.express(self.kids_shown())
        if self.prec > prec or (self.prec == prec and self.assoc == assoc and assoc == tilt):
            return s
        else:
            return "(" + s + ")"


class scalaBinOp(scalaExpr):
    def __init__(self, name, left, right):
        (prec, assoc) = scalaBinOp.prioassoc(name)
        scalaExpr.__init__(self, children = (left, right), prec = prec, assoc = assoc)

    def tilts(self):
        return (-1, 1)

    @classmethod
    def prioassoc(self, name):
        if name[-1] == ":":
            assoc = 1
        else:
            assoc = -1
        if name[-1] == "=" and name[0] != "=" and name != "<=" and name != ">=" and name != "!=":
            prec = 1
        elif name[0].isalpha:
            prec = 3
        elif name[0] == '|':
            prec = 4
        elif name[0] == '^':
            prec = 5
        elif name[0] == '&':
            prec = 6
        elif name[0] == '!':
            prec = 7
        elif name[0] == "<" or name == ">":
            prec = 8
        elif name[0] == "=":
            prec = 9 # best guess; see http://article.gmane.org/gmane.comp.lang.scala/24402
        elif name[0] == "+" or name[0] == "-":
            prec = 10
        elif name[0] == "*" or name[0] == "/" or name[0] == "%":
            prec = 11
        else:
            prec = 12
        return (prec, assoc)

class scalaPrefixOp(scalaExpr):
    def __init__(self, name, arg):
        scalaExpr.init(self, children = (arg,), prec = 12, assoc = assoc)

class scalaStmt(scala):
    pass

class scalaStmts(scalaStmt):
    def __init__(self, body = ()):
        self.body = body

    def show(self, indent = '', prefix = ''):
        return "{" + prefix + "\n" + "\n".join(n.show(indent = indent + '  ') for n in self.body) + "\n" + indent + "}"

    def show_arglists(self, arglists):
        return ''.join(self.show_arglist(x) for x in arglists)

    def show_arglist(self, arglist):
        return '(' + ', '.join(x.show() for x in arglist) + ')'

class scalaTemplate(scalaStmts):
    def __init__(self, traits = (), selfname = 'this', selftype = None, body = ()):
        scalaStmts.__init__(self, body = body)
        self.traits = traits
        self.selfname = selfname
        self.selftype = selftype

    def show(self, indent = ''):
        pfx = ''
        if self.selftype is not None or self.selfname != 'this':
            if self.selftype is not None:
                pfx = ': ' + self.selftype.show()
            pfx = self.selfname + pfx + ' => '
        return ' with '.join(p.show() for p in self.parents) + ' ' + scalaStmts.show(self, indent = indent, prefix = pfx)

# c3 a = a : merge (filter (not . null) $ map c3 (kids a) ++ [kids a])
#
# merge [] = []
# merge xss = goodhead : merge (filter (not . null) . map (dropWhile (goodhead ==)) xss)
#   where
#     goodhead = head goodheads
#     goodheads = nub (map head xss) \\ concat (map tail xss)
#
# scalin a = a : merge2 (map scalin (kids a))
#
# merge2 [] = []
# merge2 ([]:xss) = merge2 xss
# merge2 ((x:xs):xss) | x `elem` concat xss = merge2 (xs:xss)
#                     | otherwise = x : merge2 (xs:xss)

class scalaClassDef(scalaTemplate):
    def __init(self, name, parents = (), typarams = (), arglists = (), access = (), annots = (), selfname = 'this', selftype = None, body = ()):
        scalaTemplate.__init__(self, traits = parents, selfname = selfname, selftype = selftype, body = body)
        self.name = name
        self.typarams = typarams
        self.arglists = arglists
        self.access = access
        self.annots = annots

    def show(self, indent = ''):
        ret = indent + "class " + self.name
        if len(self.typarams) > 0:
            ret = ret + "[" + ", ".join(x.show() for x in typarams)
        for x in self.annots:
            ret = ret + " " + x.show()
        if len(self.access) > 0:
            ret = ret + " " + self.access[0]
            if len(self.access) > 1:
                ret = ret + "[" + self.access[1] + "]"
        ret = ret + self.show_arglists(self.arglists)
        ret = ret + " extends " + scalaTemplate.show(indent = indent)
        return ret

class scalaTraitDef(scalaTemplate):
    def __init(self, name, parents = (), typarams = (), selfname = 'this', selftype = None, body = ()):
        scalaTemplate.__init__(self, traits = parents, selfname = selfname, selftype = selftype, body = body)
        self.name = name
        self.typarams = typarams

    def show(self, indent = ''):
        ret = indent + "trait " + self.name
        if len(self.typarams) > 0:
            ret = ret + "[" + ", ".join(x.show() for x in typarams)
        ret = ret + " extends " + scalaTemplate.show(indent = indent)
        return ret

class scalaObjectDef(scalaTemplate):
    def __init(self, name, parents = (), typarams = (), selfname = 'this', selftype = None, body = ()):
        scalaTemplate.__init__(self, traits = parents, selfname = selfname, selftype = selftype, body = body)
        self.name = name
        self.typarams = typarams

    def show(self, indent = ''):
        ret = indent + "object " + self.name
        if len(self.typarams) > 0:
            ret = ret + "[" + ", ".join(x.show() for x in typarams)
        ret = ret + " extends " + scalaTemplate.show(indent = indent)
        return ret

class scalaPackageObjectDef(scalaTemplate):
    def __init(self, name, parents = (), typarams = (), selfname = 'this', selftype = None, body = ()):
        scalaTemplate.__init__(self, traits = parents, selfname = selfname, selftype = selftype, body = body)
        self.name = name
        self.typarams = typarams

    def show(self, indent = ''):
        ret = indent + "package object " + self.name
        if len(self.typarams) > 0:
            ret = ret + "[" + ", ".join(x.show() for x in typarams)
        ret = ret + " extends " + scalaTemplate.show(indent = indent)
        return ret

class scalaDoc(scalaStmt):
    def __init__(self, target, doc):
        self.target = target
        self.doc = doc

    def show(self, indent = ''):
        ret = ''
        starz = '/** '
        for l in self.doc.split("\n"):
            ret = ret + indent + starz + l + "\n"
            starz = '  * '
        ret = ret + indent + "  */\n" + self.target.show(indent = indent)
        return ret

class scalaAnnotStmt(scalaStmt):
    def __init__(self, target, annots):
        self.target = target
        self.doc = doc

    def show(self, indent = ''):
        ret = ''
        for a in self.annots:
            ret = ret + indent + a.show() + "\n"
        ret = ret + self.target.show(indent = indent)

class scalaAnnotation(scala):
    def __init__(self, body):
        self.body = body

    def show(self):
        return '@' + self.body.show()

class node_xlator(ast.NodeVisitor):
    def __init__(self, components):
        self.components = components
        self.indent = ''

    def has_deco(f):
        def inner(self, node, *args, **kwargs):
            ret = f(self, node, *args, **kwargs)
            if len(node.decorator_list) > 0:
                annots = tuple(scalaAnnotation(self.visit(dec) for dec in node.decorator_list))
                return scalaAnnotStmt(ret, annots)
            else:
                return ret
        return inner

    def has_docstring(f):
        def inner(self, node):
            body = node.body
            if len(body) > 0 and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Str):
                doc = body[0].value.s
                body = body[1:]
                ret = f(self, node, body)
                return scalaDoc(ret, doc=doc)
            else:
                return f(self, node, body)
        return inner

    @contextmanager
    def indented(self):
        oldindent = self.indent
        self.indent = self.indent + '  '
        yield
        self.indent = oldindent

    def say(self, x):
        print self.indent + x

    def resolve(self, mod, level):
        if level == 0:
            return mod
        elif mod is None:
            return '.'.join(self.components[0:-level])
        else:
            return '.'.join(self.components[0:-level] + (mod,))

    @has_docstring
    def visit_Module(self, node, body):
        return scalaPackageObjectDef(name='.'.join(self.components), body = tuple(self.visit(x) for x in body))

    def visit_alias(self, node):
        if node.asname is None:
            return node.name
        else:
            return node.name + " => " + node.asname

    def visit_ImportFrom(self, node):
        wherefrom = self.resolve(node.module, node.level)
        self.say("import __root__." + wherefrom + ".{" + ", ".join(self.visit(n) for n in node.names) + "}")

    def do_body(self, node, hdr):
        body = node.body
        if len(body) > 0 and isinstance(body[0], ast.Expr) and isinstance(body[0].value, ast.Str):
            cmt = body[0].value.s
            body = body[1:]
            starz = '/** '
            for l in cmt.split("\n"):
                self.say(starz + l)
                starz = '  * '
            self.say('  */')
        self.say(hdr + " {")
        with self.indented():
            for stmt in body:
                self.visit(stmt)
        self.say("}")

    def do_deco(self, node):
        for dec in node.decorator_list:
            self.say("@" + self.visit(dec))

    @has_docstring
    @has_deco
    def visit_ClassDef(self, node, body):
        parents = tuple(self.visit(base) for base in reversed(node.bases))
        decls = tuple(self.visit(x) for x in body)
        return scalaAnnotStmt(scalaTraitDef(name = node.name, parents = parents, body = decls), ())

    @has_docstring
    @has_deco
    def visit_FunctionDef(self, node):
        args = self.visit(node.args)
        self.do_body(node, "def " + node.name + "(" + args + ") = ")

    def visit_Name(self, node):
        return node.id

    def visit_Attribute(self, node):
        return self.visit(node.value) + '.' + node.attr

    def visit_Call(self, node):
        func = self.visit(node.func)
        args = tuple(self.visit(i) for i in node.args)
        keywords = tuple(self.visit(i) for i in node.keywords)
        if node.starargs is None:
            starargs = ()
        else:
            starargs = (self.visit(starargs) + ': _*',)
        if node.kwargs is None:
            kwargs = ()
        else:
            # NOTE: not valid scala syntax, there's no straightforward way to do this
            kwargs = (self.visit(starargs) + ': _**',)
        return func + "(" + ", ".join(args + keywords + starargs + kwargs) + ")"

    def visit_keyword(self, node):
        return node.arg + " = " + self.visit(node.value)

    def visit_Str(self, node):
        return repr(node.s)

    def visit_List(self, node):
        return "ArraySeq(" + ', '.join(self.visit(i) for i in node.elts) + ")"

    def visit_Assign(self, node):
        if len(node.targets) == 1:
            return scalaBinOp("=", self.visit(node.targets[0]), self.visit(node.value))
        else:
            raise ValueError("multiple-target assignment not yet supported")

    def generic_visit(self, node):
        self.say("Fields: " + repr(node._fields))
        self.say(ast.dump(node, include_attributes=True))

def xlate_file(filename, components):
    print components, filename
    with open(filename) as f:
        source = f.read()
    tree = ast.parse(source, filename, 'exec')
    xl = node_xlator(components)
    xl.visit(tree)

def break_dir(dirname):
    components = [dirname]
    while components[0]:
        components[0:1] = os.path.split(components[0])
    components[0:2] = ()
    return components

def xlate_files(arg, dirname, names):
    components = tuple(break_dir(dirname))
    for n in names:
        if n == "__init__.py":
            xlate_file(os.path.join(dirname,n), components)
        elif n.endswith(".py"):
            xlate_file(os.path.join(dirname,n), components + (n[0:-3],))

os.path.walk('lib', xlate_files, 0)
