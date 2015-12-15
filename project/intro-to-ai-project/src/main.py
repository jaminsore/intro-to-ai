'''
Created on Dec 12, 2015

@author: benjamin
'''
from __future__ import division

from aima import csp
from aima import search
from aima import agents

from itertools import product, groupby, combinations
from operator import itemgetter
from collections import defaultdict, Counter
import random
import re
import inspect
from math import ceil

import sys
sys.path.insert(0, '/home/benjamin/intro-to-ai/project/PSSA Scrambling/src')
from scrambler_NEW import Scrambler, get_pattern_key

def make_vars(nscrambles, nforms, nblocks, master=True):
    blocks = range(1, nblocks + 1)
    forms = range(1, nforms + 1)
    out_dict = {(0, i) : [0] for i in blocks}
    scrambles = range(1 if not master else 0, nscrambles + 1)
    out_dict.update({tup : scrambles[:] for tup in product(forms, blocks)})
    return out_dict


def make_neighbors(variables):
    key_func = itemgetter(0)
    sorted_by_block = sorted(variables.keys(), key=key_func)
    grped = groupby(sorted_by_block, key=key_func)
    out_dict = {}
    for _, group in grped:
        group = sorted(group)
        out_dict[group[0]] = [group[1]]
        out_dict[group[-1]] = [group[-2]]
        for i, var in enumerate(group[1:-1], start=1):
            out_dict[var] = [group[i-1], group[i+1]]
    return out_dict
            
            
def all_equal(a):
    a_it = iter(a)
    a_0 = next(a_it)
    return all(a_0 == a_i for a_i in a_it)


def iter_chunks(a, chunk_size):
    n = len(a)
    for i in range(n-chunk_size + 1):
        yield a[i:i + chunk_size]


def count_overlaps(a, b):
    return sum(a_i == b_i for a_i, b_i in zip(a, b) if a_i is not None and b_i is not None)


def to_matrix_representation(assignment):
    forms = sorted(set(form for form, _ in assignment))
    nblocks = max(block for _, block in assignment)
    rep = []
    for form in forms:
        asgnmnt = []
        for block in range(1, nblocks + 1):
            if (form, block) in assignment:
                asgnmnt.append(assignment[(form, block)])
            else:
                asgnmnt.append(None)
        rep.append(tuple(asgnmnt))
    return rep


def extract_args_as_attr(**kwds):
    def decorator(f):
        argspec = inspect.getargspec(f)
        def wrapper(*args, **kwargs):
            self = args[0]
            for var, attr in kwds.items():
                if var in kwargs:
                    setattr(self, attr, kwargs[var])
                else:
                    setattr(self, attr, args[argspec.args.index(var)])
            return f(*args, **kwargs)
        return wrapper
    return decorator


class PrintSupressor:
    def write(self, other):
        return None


def shuffle_vars(var_dict):
    for vars_ in var_dict.values():
        random.shuffle(vars_)

        
def renamer(string):
    return re.sub(r'\W+', '', string)


assign_extractor = extract_args_as_attr(assignment='_assignment')


class FormScramblingCSP(csp.CSP):
    
    def __init__(self, constraints):
        csp.CSP.__init__(self, constraints.variables, constraints.domains, 
                         constraints.neighbors, self.constraints)
        self._constraints = constraints
    
    def constraints(self, A, a, B, b):
#         print(self._assignment)
#         print A, a
#         print B, b
        return self._constraints(A, a, B, b, self._assignment)
    
    unassign = assign_extractor(csp.CSP.unassign)
    nconflicts = assign_extractor(csp.CSP.nconflicts)
    assign = assign_extractor(csp.CSP.assign)
    display = assign_extractor(csp.CSP.display)


class Constraints(object):
    
    def __init__(self, nforms, key_dict, variables, domains, neighbors,
                 key_overlaps=24, n_border=3, use_all=True, max_reuse=2, 
                 n_block_overlaps=2):
        
        self._nforms = nforms
        self._key_dict = key_dict
        self.variables = sorted(variables)
        self.domains = domains
        self.neighbors = neighbors
        self._key_overlaps = key_overlaps
        self._n_border = n_border
        self._use_all = use_all
        self._max_reuse = max_reuse
        self._n_block_overlaps = n_block_overlaps
        self._n_scrambles_per_block = self._get_n_scrambles_by_block()
    
    @classmethod
    def from_constraint_settings(cls, settings):
        return cls(
            settings.N_FORMS,
            settings.key_dict,
            settings.variables.keys(),
            settings.variables,
            settings.neighbors,
            settings.key_overlaps,
            settings.n_border,
            settings.use_all,
            settings.max_reuse,
            settings.n_block_overlaps
            
        )
    def __call__(self, A, a, B, b, assignment):
        assignment = assignment.copy()
        assignment[A] = a
        assignment[B] = b
        checks = (
            (self._check_borders, (A, a, B, b)),
            (self._check_usage, (assignment,)),
            (self._check_key_overlaps, (assignment,)),
            (self._check_block_overlaps, (assignment,))
        )
#         print self._check_borders(A, a, B, b)
#         print self._check_overlaps(assignment)
#         print self._check_usage(assignment)
#         print self._check_block_overlaps(assignment)
        return all(f(*args) for f, args in checks)

    
    def _get_n_scrambles_by_block(self):
        n_scrambles_dict = defaultdict(int)
        for (block, _) in self._key_dict:
            n_scrambles_dict[block] += 1
        return n_scrambles_dict
        
        
    def _check_borders(self, A, a, B, b):
  
        (a_form, a_block), (b_form, b_block) = A, B
        
        if a_form != b_form:
            return True
        
        if a_form == 0:
            return True
        
        end = self._n_border - 1
        
        if a_block < b_block:
            first, second = (a_block, a), (b_block, b)
        else:
            first, second = (b_block, b), (a_block, a)
        border_seq = self._key_dict[first][-end:]  + self._key_dict[second][:end]
#         print border_seq

        return not any(all_equal(chunk) for chunk in iter_chunks(border_seq, self._n_border))
    
    
    def _get_form_key_dict(self, assignment):
        form_key_dict = defaultdict(list)
        #key_dict is {(block, scramble) : answer_key}
        #assignment is {(form, block) : scramble}
        for (form, block) in self.variables:
            if (form, block) in assignment:
                form_key_dict[form].append(self._key_dict[(block, assignment[(form, block)])])
            else:
                form_key_dict[form].append([])
        return form_key_dict
    
    
    def _check_key_overlaps(self, assignment):
        form_key_dict = self._get_form_key_dict(assignment)
        for form1, form2 in combinations(form_key_dict.values(), 2):
            total = sum(count_overlaps(fb1, fb2) for fb1, fb2 in zip(form1, form2))
            if total > self._key_overlaps:
                return False
        return True
    
    
    def _check_usage(self, assignment):
        used_vars = defaultdict(Counter)
        for (_, block), pattern in assignment.items():
            used_vars[block][pattern] += 1
            if used_vars[block][pattern] > self._max_reuse:
                return False
            
        if self._use_all:
            for block, counts in used_vars.items():
                n_assigned = sum(counts.values())
                n_scrambles_needed = self._n_scrambles_per_block[block]
                n_scrambles_used = len(counts.keys())
                n_forms_remaining = (self._nforms - n_assigned)
                if (n_scrambles_needed - n_scrambles_used) > n_forms_remaining:
                    return False 
        return True
    
    
    def _check_block_overlaps(self, assignment):
        matrix_rep = to_matrix_representation(assignment)
        pairs = combinations(matrix_rep, 2)
        return all(count_overlaps(a, b) <= self._n_block_overlaps  for a, b in pairs)
    

class ConstraintSettings(object):
    
    COLS_SCRAMBLE = [1, 2, 3, 4]
    COL_BLOCK = 'Block'
    COL_SEQUENCE = 'ItemSeq'
    COL_KEY = 'Key'
    COL_ITEM_ID = 'UniqueItemIdentifier'
    N_FORMS = 8

    def __init__(self, scramble_df, master=True, shuffle=True, key_overlaps=27,
                 n_border=4, use_all=True, max_reuse='min', n_block_overlaps=2):
        
        if isinstance(max_reuse, str):
            max_reuse = max_reuse.lower()
            
        self._scramble_df = scramble_df
        self._key_dict = self._get_key_dict()
        self._block_scram_dict = self._get_block_scram_dict()
        self._item_seq_dict = self._get_item_seq_dict()
        self._variables = self._get_variables(master)
        self._neighbors = self._get_neighbors()
        
        self._key_overlaps = key_overlaps
        self._n_border = n_border
        self._use_all = use_all
        
        if max_reuse == 'min':
            self._max_reuse = self._get_min_reuse(master)
        else:
            self._max_reuse = max_reuse
            
        self._n_block_overlaps = n_block_overlaps
        
        if shuffle:
            shuffle_vars(self._variables)
        
    @property
    def key_dict(self):
        return self._key_dict
    
    
    @property
    def block_scram_dict(self):
        return self._block_scram_dict
    
    
    @property
    def item_seq_dict(self):
        return self._item_seq_dict
    
    
    @property
    def variables(self):
        return self._variables
    
    
    @property
    def neighbors(self):
        return self._neighbors
    
    
    @property
    def key_overlaps(self):
        return self._key_overlaps
    
    
    @property
    def n_border(self):
        return self._n_border
    
    
    @property
    def use_all(self):
        return self._use_all
    
    
    @property
    def max_reuse(self):
        return self._max_reuse
    
    
    @property
    def n_block_overlaps(self):
        return self._n_block_overlaps
    
    
    def _get_min_reuse(self, master):
        min_block = min(len(v) for v in self._block_scram_dict.values())
        if not master:
            min_block -= 1
        return int(ceil(self.N_FORMS / min_block))
    
    def _get_key_dict(self):
        k = self.COL_KEY
        b = self.COL_BLOCK
        scs = self.COLS_SCRAMBLE
        
        out = {}
        for block, df in self._scramble_df.groupby(b):
            out[(block, 0)] = df[k].values.tolist()
            out.update({(block, sc) : df[k][df[sc].values].tolist() for sc in scs})
        return out


    def _get_block_scram_dict(self):
        block_scram_dict = defaultdict(dict)
        b = self.COL_BLOCK
        scs = self.COLS_SCRAMBLE
        s = self.COL_SEQUENCE
        
        for block, block_df in self._scramble_df.groupby(b):
            block_scram_dict[block][0] = tuple((block, scram_seq) for scram_seq in block_df.index.get_level_values(s).tolist())
            for scram in scs:
                block_scram_dict[block][scram]  = \
                    tuple((block, scram_seq) for scram_seq in block_df[scram].tolist())
        return block_scram_dict


    def _get_item_seq_dict(self):
        by_block = self._scramble_df.set_index(self.COL_BLOCK, append=True).reorder_levels((1, 0), axis=0)
        by_block.sort_index(inplace=True)
        cols = [self.COL_ITEM_ID, self.COL_KEY]
        return {k : tuple(str(v[col]) if isinstance(v[col], unicode) else v[col] 
                          for col in cols) 
                for k, v in by_block[cols].T.to_dict().items()}
    
    
    def _get_variables(self, master):
        n_scrambles = len(self.COLS_SCRAMBLE)
        n_forms = self.N_FORMS - 1
        n_blocks = len(set(block for block, _ in  self._key_dict))
        return make_vars(n_scrambles, n_forms, n_blocks, master)
    
    
    def _get_neighbors(self):
#         return csp.UniversalDict(self._variables.keys())
        return make_neighbors(self._variables)
    

class Scrambler(Scrambler):

    @classmethod
    def from_constraint_settings(cls, settings, kept=None, maxrestarts=50, maxits=1000, nopts=4):
        return cls(
            settings.item_seq_dict,
            settings.block_scram_dict,
            settings.n_block_overlaps + 1,
            settings.key_overlaps + 1,
            settings.n_border,
            settings.N_FORMS - 1,
            settings.use_all,
            kept,
            maxits,
            nopts,
            settings.max_reuse,
            maxrestarts
        )
        
