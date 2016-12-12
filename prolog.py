# -*- coding: utf-8 -*-
from __future__ import absolute_import, division, print_function
from __future__ import unicode_literals
from builtins import (ascii, bytes, chr, dict, filter, hex, input,
                      int, map, next, oct, open, pow, range, round,
                      str, super, zip)

import itertools, operator
from functools import total_ordering

class Term(object):
	"""docstring for Term"""
	_ordering = {Variable: 0, PythonTerm: 10, Atom: 20, CompoundTerm: 30}
	def __init__(self, arg):
		super(Term, self).__init__()
		self.arg = arg

	def __cmp__(self, other):
		return _ordering[type(other)] - _ordering[type(self)]

	def is_list(self):
		return False

@total_ordering
class PythonTerm(Term):
	"""wrapper for any Python object"""
	def __init__(self, value):
		super(Term, self).__init__()
		self.value = value

	def __lt__(self, other):
		if isinstance(other, PythonTerm):
			return self.value < other.value
		else:
			return super(Term, self).__lt__(other)

	def __eq__(self, other):
		if isinstance(other, PythonTerm):
			return self.value == other.value
		else:
			return super(Term, self).__eq__(other)

class Atom(Term):
	"""docstring for Atom"""
	table = dict()
	def __init__(self, symbol):
		super(Atom, self).__init__()
		self.symbol = symbol
		Atom.table[symbol] = self

	def __iter__(self):
		if self.symbol == "[]":
			return ().__iter__()
		else:
			raise asfasda # TODO

	def is_list(self):
		return self.symbol == "[]"

	@classmethod
	def intern(symbol):
		if symbol not in Atom.table:
			Atom.table[symbol] = Atom(symbol)
		return Atom.table[symbol]

class Variable(Term):
	"""docstring for Variable"""
	def __init__(self, rep):
		super(Variable, self).__init__()
		self.rep = rep
	def is_bound(self):
		return self.ref is not self
	def deref(self):
		if isinstance(self.ref, Variable) and self.ref is not self:
			return self.ref.deref()
		else:
			return self.ref

class CompoundTerm(Term):
	"""docstring for CompoundTerm"""
	def __init__(self, functor, args=()):
		super(CompoundTerm, self).__init__()
		self.functor = functor
		self.args = args

	def __iter__(self):
		if self.functor is '.' and len(self.args) == 2:
			cons = self
			while cons.functor is '.' and len(cons.args) == 2:
				yield cons.args[0]
				cons = cons.args[1]
		else:
			raise asdf(asdf) # TODO

	def is_list(self):
		return self.functor is '.' and len(self.args) == 2

class Clause(object):
	"""docstring for Clause"""
	def __init__(self, head, body=()):
		super(Clause, self).__init__()
		self.head = head # a CompoundTerm
		self.body = body # a list of CompoundTerm
		
class Frame(object):
	"""docstring for Frame"""
	def __init__(self, bindings={}):
		"""
		bindings maps `Variable`s to what `Term`s they're bound to
		"""
		super(Frame, self).__init__()
		self.bindings = bindings

	@accepts(Frame, Variable)
	@returns(Term)
	def deref(self, var):
		val = var
		while val in self.bindings:
			val = self.bindings[val]
		return val

	def bound(self, x, y):
		if x <= y:
			a = x
			b = y
		else:
			a = y
			b = x
		while a in self.bindings:
			if b == self.bindings[a]:
				return True
		return False

	def copy(self):
		return Frame(self.bindings.copy())

	@accepts(Frame, dict)
	@returns(Frame)
	def extend(self, bindings):
		newFrame = self.copy()
		for a,b in bindings:
			l = [a]
			while l[-1] in newFrame.bindings:
				l.append(newFrame.bindings[l[-1]])
			l.append(b)
			while l[-1] in newFrame.bindings:
				l.append(newFrame.bindings[l[-1]])
			sl = sorted(l)
			for i in range(0, len(sl), 2):
				newFrame.bindings[sl[i]] = newFrame.bindings[sl[i+1]]
			if len(sl) % 2 == 1:
				newFrame.bindings[sl[-2]] = newFrame.bindings[sl[-1]]
		return newFrame

	@accepts(Frame, Term, Term)
	@returns(Frame)
	def unify(self, x, y):
		# a <= b in standard order of terms
		# Variable < PythonTerm < Atom < CompoundTerm
		if x <= y:
			a = x
			b = y
		else:
			a = y
			b = x

		if isinstance(a, Variable):
			if isinstance(b, Variable):
				da = self.deref(a)
				db = self.deref(b)
				if da == db:
					return self
				elif instanceof(da, Variable) or instanceof(db, Variable):
					return self.extend({a: b})
				else:
					return None
			else:
				da = self.deref(a)
				if da == b:
					return self
				elif instanceof(da, Variable):
					return self.extend({a: b})
				else:
					return None

		elif isinstance(a, PythonTerm):
			return self if isinstance(b, PythonTerm) and a == b else None

		elif isinstance(a, Atom):
			return self if instanceof(b, Atom) and a is b else None
				
		elif isinstance(a, CompoundTerm):
			# b must also be CompoundTerm
			
	# end def unify
# end class Frame

class Runtime(object):
	"""docstring for Runtime"""
	def __init__(self, arg):
		super(Runtime, self).__init__()
		self.arg = arg
		self.clauses = {} # dict from (pred name, arity) tuples to lists of Clauses
		self.trace = False
		self.debug = False
		self.stack = []

	def call_goal(self, goal, inFrame=Frame()):
		for clause in itertools.chain.from_iterable(self.clauses[(goal.functor, len(goal.args))]):
			u = inFrame.unify(clause.head, goal)
			if u:
				for subgoal in clause.body:
					for frame in self.call_goal(subgoal, u):
						yield frame


		