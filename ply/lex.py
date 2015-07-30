# -----------------------------------------------------------------------------
# ply: lex.py
#
# Copyright (C) 2001-2015,
# David M. Beazley (Dabeaz LLC)
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
# * Redistributions of source code must retain the above copyright notice,
#   this list of conditions and the following disclaimer.
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
# * Neither the name of the David Beazley or Dabeaz LLC may be used to
#   endorse or promote products derived from this software without
#  specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
# -----------------------------------------------------------------------------

__version__ = '3.6'
__tabversion__ = '3.5'

import re
import sys
import types
import copy
import os
import inspect
from collections import namedtuple

# This tuple contains known string types
try:
    # Python 2.6
    StringTypes = (types.StringType, types.UnicodeType)
except AttributeError:
    # Python 3.0
    StringTypes = (str, bytes)

# This regular expression is used to match valid token names
_is_identifier = re.compile(r'^[a-zA-Z0-9_]+$')


class LexError(Exception):
    """
    Exception thrown when invalid token encountered and no default error
    handler is defined.
    """
    def __init__(self, message, s):
        self.args = (message,)
        self.text = s


class LexToken(object):
    """ Token class.  This class is used to represent the tokens produced. """

    def __init__(self, type="", value=None, lineno=-1, lexpos=-1, lexer=None):
        self.type = type
        self.value = value
        self.lineno = lineno
        self.lexpos = lexpos
        self.lexer = lexer

    def __str__(self):
        return 'LexToken(%s,%r,%d,%d)' % (self.type, self.value, self.lineno, self.lexpos)

    def __repr__(self):
        return str(self)


class PlyLogger(object):
    """
    This object is a stand-in for a logging object created by the
    logging module.
    """
    def __init__(self, f):
        self.f = f

    def critical(self, msg, *args, **kwargs):
        self.f.write((msg % args) + '\n')

    def warning(self, msg, *args, **kwargs):
        self.f.write('WARNING: ' + (msg % args) + '\n')

    def error(self, msg, *args, **kwargs):
        self.f.write('ERROR: ' + (msg % args) + '\n')

    info = critical
    debug = critical


class NullLogger(object):
    """ Null logger is used when no output is generated. Does nothing. """
    def __getattribute__(self, name):
        return self

    def __call__(self, *args, **kwargs):
        return self


# Master regular expression. This is a list of tuples (re, findex) where re is a compiled regular expression and findex is a list mapping regex group numbers to rules
# Current regular expression strings
# Ignored characters
# Error rule (if any)
# EOF rule (if any)
LexState = namedtuple('LexState', ['re', 'retext', 'ignore', 'errorf', 'eoff'])

class Lexer:
    """
    The Lexer class implements the lexer runtime.   There are only
    a few public methods and attributes:

       input()          -  Store a new string in the lexer
       token()          -  Get the next token
       clone()          -  Clone the lexer

       lineno           -  Current line number
       lexpos           -  Current position in the input string
    """
    def __init__(self, optimize):
        self._state = LexState(None, None, '', None, None)
        self._states = {}

        self.lexstaterenames = {}  # Dictionary mapping lexer states to symbol names
        self.lexstate = None       # Current lexer state
        self.lexstatestack = []    # Stack of lexer states
        self.lexstateinfo = None   # State information
        self.lexreflags = 0        # Optional re compile flags
        self.lexdata = None        # Actual input data (as a string)
        self.lexpos = 0            # Current position in input text
        self.lexlen = 0            # Length of the input text
        self.lextokens = None      # List of valid tokens
        self.lexliterals = ''      # Literal characters that can be passed through
        self.lexmodule = None      # Module
        self.lineno = 1            # Current line number
        self.lexoptimize = optimize   # Optimized mode

    def clone(self, object=None):
        c = copy.copy(self)

        # If the object parameter has been supplied, it means we are attaching the
        # lexer to a new object.  In this case, we have to rebind all methods in
        # the lexstatere and lexstateerrorf tables.

        if object:
            newtab = {}

            new_states = {}
            for statename, state in self._states.items():
                re = state.re
                newre = []
                for cre, findex in ritem:
                    newfindex = []
                    for f in findex:
                        if not f or not f[0]:
                            newfindex.append(f)
                            continue
                        newfindex.append((getattr(object, f[0].__name__), f[1]))
                newre.append((cre, newfindex))
                errorf = getattr(object, state.errorf.__name__)
                new_states[state] = LexState(newre, state.retext, state.ignore, errorf, state.eoff)
            c._states = new_states

            c.lexmodule = object
        return c

    def writetab(self, lextab, outputdir=''):
        """ Write lexer information to a table file. """
        if isinstance(lextab, types.ModuleType):
            raise IOError("Won't overwrite existing lextab module")
        basetabmodule = lextab.split('.')[-1]
        filename = os.path.join(outputdir, basetabmodule) + '.py'
        with open(filename, 'w') as tf:
            tf.write('# %s.py. This file automatically created by PLY (version %s). Don\'t edit!\n' % (basetabmodule, __version__))
            tf.write('_tabversion   = %s\n' % repr(__tabversion__))
            tf.write('_lextokens    = %s\n' % repr(self.lextokens))
            tf.write('_lexreflags   = %s\n' % repr(self.lexreflags))
            tf.write('_lexliterals  = %s\n' % repr(self.lexliterals))
            tf.write('_lexstateinfo = %s\n' % repr(self.lexstateinfo))

            # Rewrite the lexstatere table, replacing function objects with function names
            tabre = {}
            for statename, state in self._states.items():
                titem = []
                for (pat, func), retext, renames in zip(state.re, state.retext, self.lexstaterenames[statename]):
                    titem.append((retext, _funcs_to_names(func, renames)))
                tabre[statename] = titem

            tf.write('_lexstatere   = %s\n' % repr(tabre))
            tf.write('_lexstateignore = %s\n' % repr({statename: state.ignore for statename, state in self._states.items()}))

            taberr = {}
            tabeof = {}
            for statename, state in self._states.items():
                errorf = state.errorf
                eoff = state.eoff
                taberr[statename] = errorf.__name__ if errorf else None
                tabeof[statename] = eoff.__name__ if eoff else None
            tf.write('_lexstateerrorf = %s\n' % repr(taberr))
            tf.write('_lexstateeoff = %s\n' % repr(tabeof))

    def readtab(self, tabfile, fdict):
        """ Read lexer information from a tab file """
        if isinstance(tabfile, types.ModuleType):
            lextab = tabfile
        else:
            exec('import %s' % tabfile)
            lextab = sys.modules[tabfile]

        if getattr(lextab, '_tabversion', '0.0') != __tabversion__:
            raise ImportError('Inconsistent PLY version')

        self.lextokens = lextab._lextokens
        self.lexreflags = lextab._lexreflags
        self.lexliterals = lextab._lexliterals
        self.lextokens_all = self.lextokens | set(self.lexliterals)
        self.lexstateinfo = lextab._lexstateinfo
        lexstateignore = lextab._lexstateignore
        lexstatere = {}
        lexstateretext = {}
        for statename, lre in lextab._lexstatere.items():
            titem = []
            txtitem = []
            for pat, func_name in lre:
                titem.append((re.compile(pat, lextab._lexreflags | re.VERBOSE), _names_to_funcs(func_name, fdict)))

            lexstatere[statename] = titem
            lexstateretext[statename] = txtitem

        lexstateerrorf = {}
        for statename, ef in lextab._lexstateerrorf.items():
            lexstateerrorf[statename] = fdict.get(ef, None)

        lexstateeoff = {}
        for statename, ef in lextab._lexstateeoff.items():
            lexstateeoff[statename] = fdict.get(ef, None)

        for statename in lextab._lexstatere:
            re_ = lexstatere[statename]
            retext = lexstateretext[statename]
            ignore = lexstateignore.get(statename, '')
            errorf = lexstateerrorf.get(statename, None)
            eoff = lexstateeoff.get(statename, None)
            self._states[statename] = LexState(re_, retext, ignore, errorf, eoff)

        self.begin('INITIAL')

    def input(self, s):
        """ Push a new string into the lexer. """
        # Pull off the first character to see if s looks like a string
        c = s[:1]
        if not isinstance(c, StringTypes):
            raise ValueError('Expected a string')
        self.lexdata = s
        self.lexpos = 0
        self.lexlen = len(s)

    def begin(self, state):
        """ Changes the lexing state. """
        self.lexstate = state
        self._state = self._states[state]

    def push_state(self, state):
        """ Changes the lexing state and saves old on stack. """
        self.lexstatestack.append(self.lexstate)
        self.begin(state)

    def pop_state(self):
        """ Restores the previous state. """
        self.begin(self.lexstatestack.pop())

    def current_state(self):
        """ Returns the current lexing state. """
        return self.lexstate

    def skip(self, n):
        """ Skip ahead n characters. """
        self.lexpos += n

    def token(self):
        """
        Return the next token from the Lexer

        Note: This function has been carefully implemented to be as fast
        as possible.  Don't make changes unless you really know what
        you are doing
        """
        # Make local copies of frequently referenced attributes
        lexpos = self.lexpos
        lexlen = self.lexlen
        lexignore = self._state.ignore
        lexdata = self.lexdata

        while lexpos < lexlen:
            # This code provides some short-circuit code for whitespace, tabs, and other ignored characters
            if lexdata[lexpos] in lexignore:
                lexpos += 1
                continue

            # Look for a regular expression match
            for lexre, lexindexfunc in self._state.re:
                m = lexre.match(lexdata, lexpos)
                if not m:
                    continue

                # Create a token for return
                func, type_ = lexindexfunc[m.lastindex]
                tok = LexToken(type_, m.group(), self.lineno, lexpos, self)

                if not func:
                    # If no token type was set, it's an ignored token
                    if tok.type:
                        self.lexpos = m.end()
                        return tok
                    else:
                        lexpos = m.end()
                        break

                lexpos = m.end()

                # If token is processed by a function, call it
                self.lexmatch = m
                self.lexpos = lexpos

                newtok = func(tok)

                # Every function must return a token, if nothing, we just move to next token
                if not newtok:
                    lexpos = self.lexpos         # This is here in case user has updated lexpos.
                    lexignore = self._state.ignore      # This is here in case there was a state change
                    break

                # Verify type of the token.  If not in the token map, raise an error
                if not self.lexoptimize:
                    if newtok.type not in self.lextokens_all:
                        raise LexError("%s:%d: Rule '%s' returned an unknown token type '%s'" % (
                            func.__code__.co_filename, func.__code__.co_firstlineno,
                            func.__name__, newtok.type), lexdata[lexpos:])

                return newtok
            else:
                # No match, see if in literals
                if lexdata[lexpos] in self.lexliterals:
                    self.lexpos = lexpos + 1
                    return LexToken(lexdata[lexpos], lexdata[lexpos], self.lineno, lexpos)
                # No match. Call t_error() if defined.
                elif self._state.errorf:
                    tok = LexToken('error', self.lexdata[lexpos:], self.lineno, lexpos, self)
                    self.lexpos = lexpos
                    newtok = self._state.errorf(tok)
                    if lexpos == self.lexpos:
                        # Error method didn't change text position at all. This is an error.
                        raise LexError("Scanning error. Illegal character '%s'" % (lexdata[lexpos]), lexdata[lexpos:])
                    lexpos = self.lexpos
                    if not newtok:
                        continue
                    return newtok
                else:
                    self.lexpos = lexpos
                    raise LexError("Illegal character '%s' at index %d" % (lexdata[lexpos], lexpos), lexdata[lexpos:])

        if self._state.eoff:
            tok = LexToken('eof', '', self.lineno, lexpos, self)
            self.lexpos = lexpos
            return self._state.eoff(tok)

        self.lexpos = lexpos + 1
        if self.lexdata is None:
            raise RuntimeError('No input string given with input()')
        return None

    def __iter__(self):
        return self

    def next(self):
        t = self.token()
        if t is None:
            raise StopIteration
        return t

    __next__ = next

# -----------------------------------------------------------------------------
#                           ==== Lex Builder ===
#
# The functions and classes below are used to collect lexing information
# and build a Lexer object from it.
# -----------------------------------------------------------------------------


def _get_regex(func):
    """
    Returns the regular expression assigned to a function either as a doc string
    # or as a .regex attribute attached by the @TOKEN decorator.
    """
    return getattr(func, 'regex', func.__doc__)


def get_caller_module_dict(levels):
    """
    This function returns a dictionary containing all of the symbols defined within
    a caller further down the call stack.  This is used to get the environment
    associated with the yacc() call if none was provided.
    """
    f = sys._getframe(levels)
    ldict = f.f_globals.copy()
    if f.f_globals != f.f_locals:
        ldict.update(f.f_locals)
    return ldict


def _funcs_to_names(funclist, namelist):
    """
    Given a list of regular expression functions, this converts it to a list
    suitable for output to a table file.
    """
    result = []
    for f, name in zip(funclist, namelist):
        if f and f[0]:
            result.append((name, f[1]))
        else:
            result.append(f)
    return result


def _names_to_funcs(namelist, fdict):
    """
    Given a list of regular expression function names, this converts it back to  functions.
    """

    result = []
    for n in namelist:
        if n and n[0]:
            result.append((fdict[n[0]], n[1]))
        else:
            result.append(n)
    return result


def _form_master_re(relist, reflags, ldict, toknames):
    """
    This function takes a list of all of the regex components and attempts to
    form the master regular expression.  Given limitations in the Python re
    module, it may be necessary to break the master regex into separate expressions.
    """
    if not relist:
        return []
    regex = '|'.join(relist)
    try:
        lexre = re.compile(regex, re.VERBOSE | reflags)

        # Build the index to function map for the matching engine
        lexindexfunc = [None] * (max(lexre.groupindex.values()) + 1)
        lexindexnames = lexindexfunc[:]

        for f, i in lexre.groupindex.items():
            handle = ldict.get(f, None)
            if type(handle) in (types.FunctionType, types.MethodType):
                lexindexfunc[i] = (handle, toknames[f])
                lexindexnames[i] = f
            elif handle is not None:
                lexindexnames[i] = f
                if f.find('ignore_') > 0:
                    lexindexfunc[i] = (None, None)
                else:
                    lexindexfunc[i] = (None, toknames[f])

        return [(lexre, lexindexfunc)], [regex], [lexindexnames]
    except Exception:
        m = int(len(relist) / 2)
        if m == 0:
            m = 1
        llist, lre, lnames = _form_master_re(relist[:m], reflags, ldict, toknames)
        rlist, rre, rnames = _form_master_re(relist[m:], reflags, ldict, toknames)
        return (llist + rlist), (lre + rre), (lnames + rnames)


def _statetoken(s, names):
    """
    Given a declaration name s of the form "t_" and a dictionary whose keys are
    state names, this function returns a tuple (states,tokenname) where states
    is a tuple of state names and tokenname is the name of the token.  For example,
    calling this with s = "t_foo_bar_SPAM" might return (('foo','bar'),'SPAM')
    """
    nonstate = 1
    parts = s.split('_')
    for i, part in enumerate(parts[1:], 1):
        if part not in names and part != 'ANY':
            break

    if i > 1:
        states = tuple(parts[1:i])
    else:
        states = ('INITIAL',)

    if 'ANY' in states:
        states = tuple(names)

    tokenname = '_'.join(parts[i:])
    return (states, tokenname)


class _LexerReflect(object):
    """
    This class represents information needed to build a lexer as extracted from a
    user's input file.
    """
    def __init__(self, ldict, log=None, reflags=0, optimize=False, debug=False, debuglog=None, errorlog=None):
        self.ldict = ldict
        self.error_func = None
        self.tokens = []
        self.reflags = reflags
        self.stateinfo = {'INITIAL': 'inclusive'}
        self.modules = set()
        self.error = False
        self.log = PlyLogger(sys.stderr) if log is None else log
        self._get_all()
        if not optimize:
            if self._validate_all():
                raise SyntaxError("Can't build lexer")

        # Dump some basic debugging information
        if debug:
            debuglog.info('lex: tokens   = %r', self.tokens)
            debuglog.info('lex: literals = %r', self.literals)
            debuglog.info('lex: states   = %r', self.stateinfo)

        # Check state information for ignore and error rules
        for s, stype in self.stateinfo.items():
            if stype == 'exclusive':
                if s not in self.errorf:
                    errorlog.warning("No error rule is defined for exclusive state '%s'", s)
                if s not in self.ignore and self.ignore.get('INITIAL', ''):
                    errorlog.warning("No ignore rule is defined for exclusive state '%s'", s)
            elif stype == 'inclusive':
                if s not in self.errorf:
                    self.errorf[s] = self.errorf.get('INITIAL', None)
                if s not in self.ignore:
                    self.ignore[s] = self.ignore.get('INITIAL', '')

    # Get all of the basic information
    def _get_all(self):
        self._get_tokens()
        self._get_literals()
        self._get_states()
        self._get_rules()

    # Validate all of the information
    def _validate_all(self):
        self._validate_tokens()
        self._validate_literals()
        self._validate_rules()
        return self.error

    # Get the tokens map
    def _get_tokens(self):
        tokens = self.ldict.get('tokens', None)
        if not tokens:
            self.log.error('No token list is defined')
            self.error = True
            return

        if not isinstance(tokens, (list, tuple)):
            self.log.error('tokens must be a list or tuple')
            self.error = True
            return

        if not tokens:
            self.log.error('tokens is empty')
            self.error = True
            return

        self.tokens = tokens

    # Validate the tokens
    def _validate_tokens(self):
        terminals = {}
        for n in self.tokens:
            if not _is_identifier.match(n):
                self.log.error("Bad token name '%s'", n)
                self.error = True
            if n in terminals:
                self.log.warning("Token '%s' multiply defined", n)
            terminals[n] = 1

    # Get the literals specifier
    def _get_literals(self):
        self.literals = self.ldict.get('literals', '')
        if not self.literals:
            self.literals = ''

    # Validate literals
    def _validate_literals(self):
        try:
            for c in self.literals:
                if not isinstance(c, StringTypes) or len(c) > 1:
                    self.log.error('Invalid literal %s. Must be a single character', repr(c))
                    self.error = True

        except TypeError:
            self.log.error('Invalid literals specification. literals must be a sequence of characters')
            self.error = True

    def _get_states(self):
        states = self.ldict.get('states', None)
        # Build statemap
        if states:
            if not isinstance(states, (tuple, list)):
                self.log.error('states must be defined as a tuple or list')
                self.error = True
            else:
                for s in states:
                    if not isinstance(s, tuple) or len(s) != 2:
                        self.log.error("Invalid state specifier %s. Must be a tuple (statename,'exclusive|inclusive')", repr(s))
                        self.error = True
                        continue
                    name, statetype = s
                    if not isinstance(name, StringTypes):
                        self.log.error('State name %s must be a string', repr(name))
                        self.error = True
                        continue
                    if statetype not in ('inclusive', 'exclusive'):
                        self.log.error("State type for state %s must be 'inclusive' or 'exclusive'", name)
                        self.error = True
                        continue
                    if name in self.stateinfo:
                        self.log.error("State '%s' already defined", name)
                        self.error = True
                        continue
                    self.stateinfo[name] = statetype

    # Get all of the symbols with a t_ prefix and sort them into various
    # categories (functions, strings, error functions, and ignore characters)
    def _get_rules(self):
        tsymbols = [f for f in self.ldict if f[:2] == 't_']

        # Now build up a list of functions and a list of strings
        self.toknames = {}        # Mapping of symbols to token names
        self.funcsym = {}        # Symbols defined as functions
        self.strsym = {}        # Symbols defined as strings
        self.ignore = {}        # Ignore strings by state
        self.errorf = {}        # Error functions by state
        self.eoff = {}        # EOF functions by state

        for s in self.stateinfo:
            self.funcsym[s] = []
            self.strsym[s] = []

        if len(tsymbols) == 0:
            self.log.error('No rules of the form t_rulename are defined')
            self.error = True
            return

        for f in tsymbols:
            t = self.ldict[f]
            states, tokname = _statetoken(f, self.stateinfo)
            self.toknames[f] = tokname

            if hasattr(t, '__call__'):
                if tokname == 'error':
                    for s in states:
                        self.errorf[s] = t
                elif tokname == 'eof':
                    for s in states:
                        self.eoff[s] = t
                elif tokname == 'ignore':
                    line = t.__code__.co_firstlineno
                    file = t.__code__.co_filename
                    self.log.error("%s:%d: Rule '%s' must be defined as a string", file, line, t.__name__)
                    self.error = True
                else:
                    for s in states:
                        self.funcsym[s].append((f, t))
            elif isinstance(t, StringTypes):
                if tokname == 'ignore':
                    for s in states:
                        self.ignore[s] = t
                    if '\\' in t:
                        self.log.warning("%s contains a literal backslash '\\'", f)

                elif tokname == 'error':
                    self.log.error("Rule '%s' must be defined as a function", f)
                    self.error = True
                else:
                    for s in states:
                        self.strsym[s].append((f, t))
            else:
                self.log.error('%s not defined as a function or string', f)
                self.error = True

        # Sort the functions by line number
        for f in self.funcsym.values():
            f.sort(key=lambda x: x[1].__code__.co_firstlineno)

        # Sort the strings by regular expression length
        for s in self.strsym.values():
            s.sort(key=lambda x: len(x[1]), reverse=True)

    # Validate all of the t_rules collected
    def _validate_rules(self):
        for state in self.stateinfo:
            # Validate all rules defined by functions

            for fname, f in self.funcsym[state]:
                line = f.__code__.co_firstlineno
                file = f.__code__.co_filename
                module = inspect.getmodule(f)
                self.modules.add(module)

                tokname = self.toknames[fname]
                if isinstance(f, types.MethodType):
                    reqargs = 2
                else:
                    reqargs = 1
                nargs = f.__code__.co_argcount
                if nargs > reqargs:
                    self.log.error("%s:%d: Rule '%s' has too many arguments", file, line, f.__name__)
                    self.error = True
                    continue

                if nargs < reqargs:
                    self.log.error("%s:%d: Rule '%s' requires an argument", file, line, f.__name__)
                    self.error = True
                    continue

                if not _get_regex(f):
                    self.log.error("%s:%d: No regular expression defined for rule '%s'", file, line, f.__name__)
                    self.error = True
                    continue

                try:
                    c = re.compile('(?P<%s>%s)' % (fname, _get_regex(f)), re.VERBOSE | self.reflags)
                    if c.match(''):
                        self.log.error("%s:%d: Regular expression for rule '%s' matches empty string", file, line, f.__name__)
                        self.error = True
                except re.error as e:
                    self.log.error("%s:%d: Invalid regular expression for rule '%s'. %s", file, line, f.__name__, e)
                    if '#' in _get_regex(f):
                        self.log.error("%s:%d. Make sure '#' in rule '%s' is escaped with '\\#'", file, line, f.__name__)
                    self.error = True

            # Validate all rules defined by strings
            for name, r in self.strsym[state]:
                tokname = self.toknames[name]
                if tokname == 'error':
                    self.log.error("Rule '%s' must be defined as a function", name)
                    self.error = True
                    continue

                if tokname not in self.tokens and tokname.find('ignore_') < 0:
                    self.log.error("Rule '%s' defined for an unspecified token %s", name, tokname)
                    self.error = True
                    continue

                try:
                    c = re.compile('(?P<%s>%s)' % (name, r), re.VERBOSE | self.reflags)
                    if c.match(''):
                        self.log.error("Regular expression for rule '%s' matches empty string", name)
                        self.error = True
                except re.error as e:
                    self.log.error("Invalid regular expression for rule '%s'. %s", name, e)
                    if '#' in r:
                        self.log.error("Make sure '#' in rule '%s' is escaped with '\\#'", name)
                    self.error = True

            if not self.funcsym[state] and not self.strsym[state]:
                self.log.error("No rules defined for state '%s'", state)
                self.error = True

            # Validate the error function
            efunc = self.errorf.get(state, None)
            if efunc:
                f = efunc
                line = f.__code__.co_firstlineno
                file = f.__code__.co_filename
                module = inspect.getmodule(f)
                self.modules.add(module)

                if isinstance(f, types.MethodType):
                    reqargs = 2
                else:
                    reqargs = 1
                nargs = f.__code__.co_argcount
                if nargs > reqargs:
                    self.log.error("%s:%d: Rule '%s' has too many arguments", file, line, f.__name__)
                    self.error = True

                if nargs < reqargs:
                    self.log.error("%s:%d: Rule '%s' requires an argument", file, line, f.__name__)
                    self.error = True

        for module in self.modules:
            self._validate_module(module)

    def _validate_module(self, module):
        """
        This checks to see if there are duplicated t_rulename() functions or strings
        in the parser input file.  This is done using a simple regular expression
        match on each line in the source code of the given module.
        """
        lines, linen = inspect.getsourcelines(module)

        fre = re.compile(r'\s*def\s+(t_[a-zA-Z_0-9]*)\(')
        sre = re.compile(r'\s*(t_[a-zA-Z_0-9]*)\s*=')

        counthash = {}
        linen += 1
        for line in lines:
            m = fre.match(line)
            if not m:
                m = sre.match(line)
            if m:
                name = m.group(1)
                prev = counthash.get(name)
                if not prev:
                    counthash[name] = linen
                else:
                    filename = inspect.getsourcefile(module)
                    self.log.error('%s:%d: Rule %s redefined. Previously defined on line %d', filename, linen, name, prev)
                    self.error = True
            linen += 1


def lex(module=None, object=None, debug=False, optimize=False, lextab='lextab',
        reflags=0, nowarn=False, outputdir=None, debuglog=None, errorlog=None):
    """
    This checks to see if there are duplicated t_rulename() functions or strings
    in the parser input file.  This is done using a simple regular expression
    match on each line in the source code of the given module.
    """
    if lextab is None:
        lextab = 'lextab'

    global lexer


    global token, input

    if errorlog is None:
        errorlog = PlyLogger(sys.stderr)

    if debug:
        if debuglog is None:
            debuglog = PlyLogger(sys.stderr)

    # Get the module dictionary used for the lexer
    if object:
        module = object

    # Get the module dictionary used for the parser
    if module:
        ldict = dict([(k, getattr(module, k)) for k in dir(module)])
        # If no __file__ attribute is available, try to obtain it from the __module__ instead
        if '__file__' not in ldict:
            ldict['__file__'] = sys.modules[ldict['__module__']].__file__
    else:
        ldict = get_caller_module_dict(2)

    # Determine if the module is package of a package or not.
    # If so, fix the tabmodule setting so that tables load correctly
    pkg = ldict.get('__package__')
    if pkg and isinstance(lextab, str):
        if '.' not in lextab:
            lextab = pkg + '.' + lextab

    if optimize and lextab:
        try:
            lexobj = Lexer(optimize)
            lexobj.readtab(lextab, ldict)
            token = lexobj.token
            input = lexobj.input
            lexer = lexobj
            return lexobj

        except ImportError:
            pass

    # Collect parser information from the dictionary
    linfo = _LexerReflect(ldict, log=errorlog, reflags=reflags, optimize=optimize,
                          debug=debug, debuglog=debuglog, errorlog=errorlog)

    # Build the master regular expressions
    lexobj = Lexer(optimize)
    lexobj.lextokens = set(linfo.tokens)
    if isinstance(linfo.literals, (list, tuple)):
        lexobj.lexliterals = type(linfo.literals[0])().join(linfo.literals)
    else:
        lexobj.lexliterals = linfo.literals
    lexobj.lextokens_all = lexobj.lextokens | set(lexobj.lexliterals)

    if debug:
        debuglog.info('lex: ==== MASTER REGEXS FOLLOW ====')

    for state in linfo.stateinfo:
        regex_list = ['(?P<%s>%s)' % (fname, _get_regex(f)) for fname, f in linfo.funcsym[state]] + \
                     ['(?P<%s>%s)' % (name, r) for name, r in linfo.strsym[state]]
        lexre, re_text, re_names = _form_master_re(regex_list, reflags, ldict, linfo.toknames)
        lexobj.lexstaterenames[state] = re_names
        if debug:
            for i, text in enumerate(re_text):
                debuglog.info("lex: state '%s' : regex[%d] = '%s'", state, i, text)
        lexobj._states[state] = LexState(lexre, re_text, linfo.ignore.get(state, ''), linfo.errorf.get(state, None), linfo.eoff.get(state, None))

    # For inclusive states, we need to add the regular expressions from the INITIAL state
    for state, stype in linfo.stateinfo.items():
        if state != 'INITIAL' and stype == 'inclusive':
            lexobj._states[state].re.extend(lexobj._states['INITIAL'].re)
            lexobj._states[state].retext.extend(lexobj._states['INITIAL'].retext)
            lexobj.lexstaterenames[state].extend(lexobj.lexstaterenames['INITIAL'])

    lexobj.lexstateinfo = linfo.stateinfo
    lexobj.lexreflags = reflags
    lexobj.begin('INITIAL')

    if not lexobj._state.errorf:
        errorlog.warning('No t_error rule is defined')

    # Create global versions of the token() and input() functions
    token = lexobj.token
    input = lexobj.input
    lexer = lexobj

    # If in optimize mode, we write the lextab
    if lextab and optimize:
        if outputdir is None:
            # If no output directory is set, the location of the output files
            # is determined according to the following rules:
            #     - If lextab specifies a package, files go into that package directory
            #     - Otherwise, files go in the same directory as the specifying module
            if isinstance(lextab, types.ModuleType):
                srcfile = lextab.__file__
            else:
                if '.' not in lextab:
                    srcfile = ldict['__file__']
                else:
                    parts = lextab.split('.')
                    pkgname = '.'.join(parts[:-1])
                    exec('import %s' % pkgname)
                    srcfile = getattr(sys.modules[pkgname], '__file__', '')
            outputdir = os.path.dirname(srcfile)
        try:
            lexobj.writetab(lextab, outputdir)
        except IOError as e:
            errorlog.warning("Couldn't write lextab module %r. %s" % (lextab, e))

    return lexobj


def runmain(lexer=None, data=None):
    """ This runs the lexer as a main program. """
    if not data:
        try:
            filename = sys.argv[1]
            f = open(filename)
            data = f.read()
            f.close()
        except IndexError:
            sys.stdout.write('Reading from standard input (type EOF to end):\n')
            data = sys.stdin.read()

    if lexer:
        _input = lexer.input
    else:
        _input = input
    _input(data)
    if lexer:
        _token = lexer.token
    else:
        _token = token

    while True:
        tok = _token()
        if not tok:
            break
        sys.stdout.write('(%s,%r,%d,%d)\n' % (tok.type, tok.value, tok.lineno, tok.lexpos))


def TOKEN(r):
    """
    This decorator function can be used to set the regex expression on a function
    when its docstring might need to be set in an alternative way
    """
    def set_regex(f):
        if hasattr(r, '__call__'):
            f.regex = _get_regex(r)
        else:
            f.regex = r
        return f
    return set_regex

# Alternative spelling of the TOKEN decorator
Token = TOKEN
