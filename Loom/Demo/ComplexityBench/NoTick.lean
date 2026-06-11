import Loom.Demo.ComplexityBench.Util

def main (args : List String) : IO Unit :=
  ComplexityBench.runNoTick ComplexityBench.linearSearchArrayIdxNoTick? args
