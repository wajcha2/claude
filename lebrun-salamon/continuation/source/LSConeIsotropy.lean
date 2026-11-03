import LSConeRadial
import LSRadialDetection
import LSConeLocalization

/-!
## Cone tangent isotropy gives the cubic diagonal and pole contradiction

SOURCE: `lines:cone-addition`. This connects the actual scaling-curve
radial tangent, projective Kahler-module detection, cubic diagonal
membership, and the existing localized rescaled-arc contradiction.

The chart is a formally smooth principal localization of the actual
vanishing-ideal quotient. Tangent isotropy remains a geometric hypothesis;
radial-form vanishing and the cubic estimate are derived conclusions.
No equation-closedness, free cotangent basis, or all-functions congruence
assumption is introduced.

Place after both `cone_radial_tangent.lean.txt` and `radial_detection.lean.txt`.
STATUS: uncompiled continuation under the user's 35,000-line build gate.
-/

noncomputable section
set_option autoImplicit false

namespace LeBrunSalamon.Construction.Lines.ConeIsotropy

open scoped TensorProduct

variable {I : Type} [Fintype I]
variable (S : Set (I → ℂ)) (hcone : ConeRadial.IsCone S)
variable (f : DirectionCones.CoordinateRing S)
variable {L : Type*} [CommRing L] [Algebra ℂ L]
variable [Algebra (DirectionCones.CoordinateRing S) L]
variable [IsScalarTower ℂ (DirectionCones.CoordinateRing S) L]
variable [IsLocalization.Away f L] [Algebra.FormallySmooth ℂ L]

include hcone f

/-- The radial vector is constructed as an actual localized point
derivation. Tangent isotropy annihilates the radial pairing, and the
smooth principal-chart detector proves equality of the Kahler form. -/
theorem radialForm_eq_zero_of_tangent_isotropy (omega : I → I → ℂ)
    (hisotropic : ∀ (p : L →ₐ[ℂ] ℂ) (D E : Infinitesimal.Tangent L p),
      ConePairing.pairing omega
        (fun i => D.val (ConeRadial.localizedCoordinate (L := L) S i))
        (fun i => E.val (ConeRadial.localizedCoordinate (L := L) S i)) = 0) :
    ConeDiagonal.radialForm (ConeRadial.localizedCoordinate (L := L) S) omega = 0 := by
  apply RadialDetection.principalConeChart_radialForm_eq_zero S f omega
  intro p D
  exact ConeRadial.radial_pairing_zero_of_tangent_isotropy S hcone
    (Submonoid.powers f) omega hisotropic p D

/-- Actual tangent isotropy on a conical smooth principal chart implies
third-order diagonal vanishing of the ambient skew pairing. -/
theorem coordinatePairing_mem_cube_of_tangent_isotropy (omega : I → I → ℂ)
    (hskew : ∀ i j, omega j i = -omega i j)
    (hisotropic : ∀ (p : L →ₐ[ℂ] ℂ) (D E : Infinitesimal.Tangent L p),
      ConePairing.pairing omega
        (fun i => D.val (ConeRadial.localizedCoordinate (L := L) S i))
        (fun i => E.val (ConeRadial.localizedCoordinate (L := L) S i)) = 0) :
    ConeDiagonal.coordinatePairing (ConeRadial.localizedCoordinate (L := L) S) omega ∈
      ConeDiagonal.diagonalIdeal L ^ 3 :=
  ConeDiagonal.coordinatePairing_mem_cube _ omega hskew
    (radialForm_eq_zero_of_tangent_isotropy S hcone f omega hisotropic)

/-- The radial identity required by the existing arc contradiction is
now proved from genuine cone tangents. The remaining inputs describe
the actual arcs and meromorphic fixed-sum family obtained by the later
geometric extraction; the theorem does not postulate their existence.

The ambient-coordinate rescaling equation supplies agreement modulo the
full pole order on every localized regular function. A nonzero constant
meromorphic pairing then has order exactly `2*k`, contradicting the
`3*k` forced by the cubic diagonal calculation. -/
theorem rescaled_nonorthogonal_arcs_impossible_of_tangent_isotropy
    (omega : I → I → ℂ) (hskew : ∀ i j, omega j i = -omega i j)
    (hisotropic : ∀ (p : L →ₐ[ℂ] ℂ) (D E : Infinitesimal.Tangent L p),
      ConePairing.pairing omega
        (fun i => D.val (ConeRadial.localizedCoordinate (L := L) S i))
        (fun i => E.val (ConeRadial.localizedCoordinate (L := L) S i)) = 0)
    {K : Type*} [CommRing K] [Algebra ℂ K]
    (p q : L →ₐ[ℂ] ConePole.Series)
    (k : ℕ) (hk : 0 < k) (s : I → ℂ)
    (hrescale : ∀ i,
      p (ConeRadial.localizedCoordinate (L := L) S i) -
      q (ConeRadial.localizedCoordinate (L := L) S i) =
        (PowerSeries.X : ConePole.Series) ^ k * PowerSeries.C (s i))
    (j : ConePole.Series →ₐ[ℂ] K) (hj : Function.Injective j)
    (a b : I → K) (c : ℂ) (hc : c ≠ 0)
    (hp : ∀ i, j (p (ConeRadial.localizedCoordinate (L := L) S i)) =
      j (PowerSeries.X : ConePole.Series) ^ k * a i)
    (hq : ∀ i, j (q (ConeRadial.localizedCoordinate (L := L) S i)) =
      -(j (PowerSeries.X : ConePole.Series) ^ k * b i))
    (hpair : ConePairing.pairing omega a b = algebraMap ℂ K c) : False :=
  ConeArcs.localized_rescaled_nonorthogonal_arcs_impossible
    (DirectionCones.vanishingIdeal S) (Submonoid.powers f) p q omega hskew
    (radialForm_eq_zero_of_tangent_isotropy S hcone f omega hisotropic)
    k hk s hrescale j hj a b c hc hp hq hpair

end LeBrunSalamon.Construction.Lines.ConeIsotropy

end
