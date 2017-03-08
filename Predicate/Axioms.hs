module Predicate.Axioms
(
     axioms,
     axiomsArithm
) where 

import Predicate.Parser

axioms = map f 
         ["F->P->F",
          "(F->P)->(F->P->R)->(F->R)",
          "F->(P->(F&P))",
          "F&P->F",
          "F&P->P",
          "F->F|P",
          "P->F|P",
          "(F->R)->(P->R)->((F|P)->R)",
          "(F->P)->(F->!P)->!F",
          "!!F->F"
          ]
          where f = parse

axiomsArithm = map parse
          ["a=b->a'=b'",
          "a=b->a=c->b=c",
          "a'=b'->a=b",
          "a+b'=(a+b)'",
          "a+0=a",
          "a*0=0",
          "a*b'=a*b+a",
          "!a'=0"]