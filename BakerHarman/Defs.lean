import Mathlib

/-! Basic definitions for reciprocal small-remainders approximation. -/

namespace BakerHarman

/-- The distance from a real number to the nearest integer. -/
noncomputable def distNearestInt (ξ : ℝ) : ℝ := |ξ - round ξ|

/-- The exponent quoted in Lemma 5 of Heyman–Shparlinski's shifted-sets paper.
Baker–Harman's original equation (2.1) uses a rounded derivative order instead;
see `BakerHarman.Exponent` for the comparison and retained numerical margin. -/
noncomputable def gammaBH (K : ℝ) : ℝ := 1 / ((2 : ℝ) ^ (2 + max 1 K) - 4)

end BakerHarman
