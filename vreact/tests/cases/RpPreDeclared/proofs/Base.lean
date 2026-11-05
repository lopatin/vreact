/-- Pre-empts the generated `bump` (adversarial: a user proof must not be able to replace a
translated declaration unnoticed). -/
@[reducible] def VTS.model.bump (x : Int) : Int := x + 2
