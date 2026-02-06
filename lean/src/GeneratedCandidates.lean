/-- Placeholder; overwritten by python/analyze_results.py. -/
import Std

structure Candidate where
  score : Float
  a : Array Float
  x0 : Float
  v : Float
  gType : String
  t0 : Float
  tau : Float
deriving Repr

def topNearMisses : List Candidate := []
