# -*- coding: utf-8 -*-
from __future__ import absolute_import, division, print_function
from __future__ import unicode_literals
from builtins import (ascii, bytes, chr, dict, filter, hex, input,
                      int, map, next, oct, open, pow, range, round,
                      str, super, zip)

import itertools, operator
from functools import total_ordering
from collections import defaultdict

@total_ordering
class Term(object):
	"""docstring for Term"""
	# _ordering = {Variable: 0, PythonTerm: 10, Atom: 20, CompoundTerm: 30}
	def __init__(self):
		super(Term, self).__init__()

	def __lt__(self, other):
		return self.order() < other.order()

	def __eq__(self, other):
		return self is other

	def order(self):
		raise NotImplementedError

	def copy(self):
		raise NotImplementedError

	def is_list(self):
		return False

@total_ordering
class Variable(Term):
	"""docstring for Variable"""
	def __init__(self, rep):
		super(Variable, self).__init__()
		self.rep = rep

	def __lt__(self, other):
		if isinstance(other, Variable):
			return id(self) < id(other)
		else:
			return super(Variable, self).__lt__(other)

	def order(self):
		return 0

	def copy(self):
		return Variable(self.rep)

@total_ordering
class PythonTerm(Term):
	"""wrapper for any Python object"""
	def __init__(self, value):
		super(Term, self).__init__()
		self.value = value

	def order(self):
		return 10

	def __lt__(self, other):
		if isinstance(other, PythonTerm):
			return self.value < other.value
		else:
			return super(Term, self).__lt__(other)

	def __eq__(self, other):
		if isinstance(other, PythonTerm):
			return self.value == other.value
		else:
			return False

	def copy(self):
		return self

@total_ordering
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
			raise TypeError # TODO

	def __lt__(self, other):
		if isinstance(other, Atom):
			return self.symbol < other.symbol
		else:
			return super(Atom, self).__lt__(other)

	def __eq__(self, other):
		if isinstance(other, Atom):
			return self is other
		else:
			return False

	def order(self):
		return 20

	def copy(self):
		return self

	def is_list(self):
		return self.symbol == "[]"

	@classmethod
	def intern(symbol):
		if symbol not in Atom.table:
			Atom.table[symbol] = Atom(symbol)
		return Atom.table[symbol]

class CompoundTerm(Term):
	"""docstring for CompoundTerm"""
	def __init__(self, functor, args=()):
		super(CompoundTerm, self).__init__()
		self.functor = functor
		self.args = args

	def __iter__(self):
		print('entered CompoundTerm iterator')
		print('functor is ', self.functor)
		print('num args ', len(self.args))
		if self.functor == '.' and len(self.args) == 2:
			print('inside if')
			cons = self
			while isinstance(cons, CompoundTerm) and cons.functor == '.' and len(cons.args) == 2:
				yield cons.args[0]
				cons = cons.args[1]
		else:
			raise TypeError # TODO

	def __lt__(self, other):
		if isinstance(other, CompoundTerm):
			if len(self.args) != len(other.args):
				return len(self.args) < len(other.args)
			elif self.functor is not other.functor:
				return self.functor < other.functor
			else:
				for i in range(len(self.args)):
					if self.args[i] != other.args[i]:
						return self.args[i] < other.args[i]
				return False
		else:
			return super(CompoundTerm, self).__lt__(other)

	def __eq__(self, other):
		if isinstance(other, CompoundTerm):
			return self is other
		else:
			return False

	def order(self):
		return 30

	def copy(self):
		return CompoundTerm(self.functor, [t.copy() for t in self.args])

	def is_list(self):
		return self.functor is '.' and len(self.args) == 2

class Clause(object):
	"""docstring for Clause"""
	def __init__(self, head, body=()):
		super(Clause, self).__init__()
		self.head = head # a CompoundTerm
		self.body = body # a list of Terms; can be CompoundTerm or PythonTerm (if the value is a function (Runtime, Frame) -> bool)
		
class Frame(object):
	"""docstring for Frame"""
	def __init__(self, bindings={}):
		"""
		bindings maps `Variable`s to what `Term`s they're bound to
		"""
		super(Frame, self).__init__()
		self.bindings = bindings

	def deref(self, term):
		val = term
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
			a = self.bindings[a]
			if b == a:
				return True
		return False

	def copy(self):
		return Frame(self.bindings.copy())

	def extend(self, bindings):
		newFrame = self.copy()
		for a,b in bindings.items():
			l = [a]
			while l[-1] in newFrame.bindings:
				l.append(newFrame.bindings[l[-1]])
			l.append(b)
			while l[-1] in newFrame.bindings:
				l.append(newFrame.bindings[l[-1]])
			# sl = sorted(l)
			# for i in range(0, len(sl), 2):
			# 	newFrame.bindings[sl[i]] = newFrame.bindings[sl[i+1]]
			# if len(sl) % 2 == 1:
			# 	newFrame.bindings[sl[-2]] = newFrame.bindings[sl[-1]]
			m = max(l)
			for var in l[:l.index(m)]:
				newFrame.bindings[var] = m
			for var in l[l.index(m)+1:]:
				newFrame.bindings[var] = m
		return newFrame

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
				elif isinstance(da, Variable) or isinstance(db, Variable):
					return self.extend({a: b})
				else:
					return None
			else:
				da = self.deref(a)
				if da == b:
					return self
				elif isinstance(da, Variable):
					return self.extend({a: b})
				else:
					return None

		elif isinstance(a, PythonTerm):
			return self if isinstance(b, PythonTerm) and a == b else None

		elif isinstance(a, Atom):
			return self if isinstance(b, Atom) and a is b else None
				
		elif isinstance(a, CompoundTerm):
			# b must also be CompoundTerm
			if a.functor == b.functor and len(a.args) == len(b.args):
				frame = self
				for i in range(len(a.args)):
					frame = frame.unify(a.args[i], b.args[i])
					if frame is None:
						return None
				return frame
			else:
				return None
		return None
	# end def unify
# end class Frame

def _builtin_repeat(runtime, frame):
	while True:
		yield frame

def _builtin_cut(runtime, frame):
	yield asf

_conjunction_var1 = Variable('Conjunct1')
_conjunction_clause = Clause(Co)

builtinPredicates = {
	('true', 0): [Clause(CompoundTerm('true'))],
	('false', 0): [Clause(CompoundTerm('false'))],
	('repeat', 0): [Clause(CompoundTerm('repeat'), [PythonTerm(_builtin_repeat)])],
	('!', 0): [Clause(CompoundTerm('!'), [PythonTerm(_builtin_cut)])],
	(',', 2): [Clause(CompoundTerm(',', [Variable('Conjunct1'), Variable('Conjunct2')]), )]
}

class Runtime(object):
	"""docstring for Runtime"""
	def __init__(self):
		super(Runtime, self, stdin, stdout, stderr).__init__()
		self.clauses = defaultdict(list, builtinPredicates) # dict from (pred name, arity) tuples to lists of Clauses
		self.trace = False
		self.debug = False
		self.stack = None
		self.clauseStream = None
		self.stdin = stdin
		self.stdout = stdout
		self.stderr = stderr

	# def call_goal(self, goal, inFrame=Frame()):
	# 	goal = inFrame.deref(goal)
	# 	if isinstance(goal, PythonTerm):
	# 			for frame in goal.value(self, inFrame)
	# 				yield frame
	# 	else:
	# 		for clause in self.clauses[(goal.functor, len(goal.args))]:
	# 			u = inFrame.unify(clause.head, goal)
	# 			if u:
	# 				for frame in itertools.ifilter()
	# 				for subgoal in clause.body:
	# 					for frame in self.call_goal(subgoal, u):
	# 						frames.append

	def call_goal(self, goal, inFrame=Frame()):
		self.stack = [(goal, inFrame)]
		self.clauseStream = None
		subgoalStream = None
		frameStream = None
		frameStack = []
		u = None
		while True:
			if 0 == len(self.stack):
				return
			elif 1 == len(self.stack):
				if len(frameStack) > 0:
					for frame in frameStack:
						yield frame
					frameStack.pop()
					self.stack.pop()
					continue
			goal, inFrame = self.stack[-1]
			goal = inFrame.deref(goal)
			if isinstance(goal, PythonTerm):
				# for frame in goal.value(self, inFrame):
				# 	yield frame
				frameStack.append(goal.value(self, inFrame))
				self.stack.pop() # return
				continue
			else:
				if frameStream:
					try:
						frame = frameStream.next()
						asdf
						continue
					except StopIteration:
						frameStream = None
				if subgoalStream:
					try:
						subgoal = subgoalStream.next()
						self.stack.append((subgoal, u)) # recursive call
						continue
					except StopIteration:
						subgoalStream = None
				if self.clauseStream:
					try:
						clause = self.clauseStream.next()
						u = inFrame.unify(clause.head, goal)
						if u:
							subgoalStream = clause.body.__iter__()
						continue
					except StopIteration:
						self.clauseStream = None
		# end while True
	# end def call_goal


		



