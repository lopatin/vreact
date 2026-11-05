/-- Pre-empts the generated `after` (whose body violates its ensures). -/
@[reducible] def VTS.kw.after (x : Int) : Int := x + 1
