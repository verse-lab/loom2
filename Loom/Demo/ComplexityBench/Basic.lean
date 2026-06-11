import Loom.Demo.ComplexityBench.Util

def main (args : List String) : IO Unit :=
  ComplexityBench.runBasic BasicRepr.CreditT.linearSearchArrayIdx? args
