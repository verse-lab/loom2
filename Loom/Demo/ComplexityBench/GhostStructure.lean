import Loom.Demo.ComplexityBench.Util

def main (args : List String) : IO Unit :=
  ComplexityBench.runGhostStructure GhostReprStructure.linearSearchArrayIdx? args
