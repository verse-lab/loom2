import Loom.Instances.MiniViper.SymExec
import Loom.Instances.MiniViper.DSL
open SExp Stmt Assert AtomicAssert PureExp PermExp Lit Binop



def verify (params : List VTyp) (fieldList : List (FieldName × VTyp)) (body : Stmt) : Bool :=
  sinit params fieldList fun σ =>
    sexec σ body fun _ => true

open DSL

def test1 : Stmt :=
  do![
    inhale! acc(x![0], "f", p![2/3]),
    inhale! acc(x![1], "f", p![2/3]),
    exhale! pure{x![0] != x![1]}
  ]


#eval verify [.tRef, .tRef] [("f", .tInt)] test1


def test2 : Stmt :=
  do![
    inhale! acc(x![0], "f", p![1]),
    exhale! acc(x![0], "f", p![1])
  ]
#eval verify [.tRef] [("f", .tInt)] test2

def test3 : Stmt :=
  do![
    inhale! acc(x![0], "f", p![1]),
    exhale! acc(x![0], "f", p![1]),
    exhale! acc(x![0], "f", p![1])
  ]

#eval verify [.tRef] [("f", .tInt)] test3

def test4 : Stmt :=
  do![
    inhale! pure{i![0] < x![0]},
    exhale! pure{i![0] < x![0]}
  ]

#eval verify [.tInt] [] test4

#eval verify [] [] .skip

def test6 : Stmt :=
  do![
    inhale! (acc(x![0], "f", p![1]) ** acc(x![1], "f", p![1])),
    exhale! acc(x![1], "f", p![1]),
    exhale! acc(x![0], "f", p![1])
  ]
#eval verify [.tRef, .tRef] [("f", .tInt)] test6

def test7 : Stmt :=
  do![
    inhale! ((acc(x![0], "f", p![1]) ** acc(x![2], "f", p![1])) ** acc(x![1], "f", p![1])),
    exhale! ((acc(x![2], "f", p![1]) ** (acc(x![0], "f", p![1]) ** acc(x![1], "f", p![1]))) ** pure{x![0] != x![1]})
  ]
#eval verify [.tRef, .tRef, .tRef] [("f", .tInt)] test7

def test8 : Stmt :=
  do![
    inhale! acc(x![0], "f", p![1]),
    exhale! pure{x![0] != x![1]}
  ]

#eval verify [.tRef, .tRef] [("f", .tInt)] test8

def test9_merge_halves_to_full : Stmt :=
  do![
    inhale! acc(x![0], "f", p![1/2]),
    inhale! acc(x![0], "f", p![1/2]),
    exhale! acc(x![0], "f", p![1])
  ]

#eval verify [.tRef] [("f", .tInt)] test9_merge_halves_to_full


def test10 : Stmt :=
  do![
    inhale! ((acc(x![0], "f", p![1]) ** pure{fld(x![0], "f") == i![0]})),
    exhale! (pure{fld(x![0], "f") == i![0]})
  ]
#eval verify [.tRef] [("f", .tInt)] test10
