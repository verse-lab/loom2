import Loom.Demo.ComplexityBench.Util

def main (args : List String) : IO Unit :=
  ComplexityBench.runGhostStateT GhostReprStateT.linearSearchArrayIdx? args
