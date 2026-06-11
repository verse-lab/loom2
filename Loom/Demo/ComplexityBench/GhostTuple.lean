import Loom.Demo.ComplexityBench.Util

def main (args : List String) : IO Unit :=
  ComplexityBench.runGhostTuple GhostReprTuple.linearSearchArrayIdx? args
