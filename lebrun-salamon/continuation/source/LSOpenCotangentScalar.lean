import LSHomVelocity

/-! Pull a scalar cotangent functional to an actual open immersion. The
normalization is proved on the original universal differentials. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton

open LeBrunSalamon.PhaseThirty

namespace LeBrunSalamon.OpenCotangentScalar

/-- The inverse of the actual open-immersion differential, followed by
pullback of the given functional and the actual structure-sheaf map. -/
def pull {T Y S : Scheme} (f : T ⟶ Y) [IsOpenImmersion f] (s : Y ⟶ S)
    (q : cotangentSheaf s ⟶ structureModule Y) :
    cotangentSheaf (f ≫ s) ⟶ structureModule T := by
  letI := openImmersion_cotangentMap_isIso f s
  exact (asIso (cotangentMap f s)).inv ≫
    (Scheme.Modules.pullback f).map q ≫ unitPullbackMap f

/-- A pulled differential is evaluated by pulling the original scalar. -/
theorem pull_differential {T Y S : Scheme} (f : T ⟶ Y) [IsOpenImmersion f]
    (s : Y ⟶ S) (q : cotangentSheaf s ⟶ structureModule Y)
    (U : Y.Opens) (a : RingSections Y U) :
    (pull f s q).app (f ⁻¹ᵁ U)
      ((cotangentPresentation (f ≫ s)).differential.apply (f ⁻¹ᵁ U) (f.app U a)) =
        f.app U (q.app U ((cotangentPresentation s).differential.apply U a)) := by
  letI := openImmersion_cotangentMap_isIso f s
  rw [← ContactDerivativeIsoProof.cotangentMap_differential]
  let z := pullLocalSection f (cotangentSheaf s) U
    ((cotangentPresentation s).differential.apply U a)
  have hz : (asIso (cotangentMap f s)).inv.app (f ⁻¹ᵁ U)
      ((cotangentMap f s).app (f ⁻¹ᵁ U) z) = z := by
    change ((cotangentMap f s) ≫ (asIso (cotangentMap f s)).inv).app (f ⁻¹ᵁ U) z = z
    rw [show cotangentMap f s ≫ (asIso (cotangentMap f s)).inv = 𝟙 _ from
      (asIso (cotangentMap f s)).hom_inv_id]
    rfl
  change (unitPullbackMap f).app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullback f).map q).app (f ⁻¹ᵁ U)
      ((asIso (cotangentMap f s)).inv.app (f ⁻¹ᵁ U)
        ((cotangentMap f s).app (f ⁻¹ᵁ U) z))) = _
  rw [hz]
  dsimp only [z]
  rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
    ContactDerivativeIsoProof.unitPullbackMap_pullLocalSection]

/-- Equality of the chosen base maps is transported through the fixed
cotangent presentation, with no new choice of differential. -/
def pullAlong {T Y S : Scheme} (f : T ⟶ Y) [IsOpenImmersion f]
    (s : Y ⟶ S) (t : T ⟶ S) (h : f ≫ s = t)
    (q : cotangentSheaf s ⟶ structureModule Y) :
    cotangentSheaf t ⟶ structureModule T :=
  eqToHom (congrArg cotangentSheaf h.symm) ≫ pull f s q

theorem pullAlong_differential {T Y S : Scheme} (f : T ⟶ Y) [IsOpenImmersion f]
    (s : Y ⟶ S) (t : T ⟶ S) (h : f ≫ s = t)
    (q : cotangentSheaf s ⟶ structureModule Y)
    (U : Y.Opens) (a : RingSections Y U) :
    (pullAlong f s t h q).app (f ⁻¹ᵁ U)
      ((cotangentPresentation t).differential.apply (f ⁻¹ᵁ U) (f.app U a)) =
        f.app U (q.app U ((cotangentPresentation s).differential.apply U a)) := by
  subst t
  exact pull_differential f s q U a

/-- Chain rule for the original cotangent map, without smoothness of either
relative source. The sole transport is the associativity of the base map. -/
theorem cotangentMap_comp {X Y Z S : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z)
    (s : Z ⟶ S) :
    (Scheme.Modules.pullbackComp f g).hom.app (cotangentSheaf s) ≫
        cotangentMap (f ≫ g) s ≫
        eqToHom (congrArg cotangentSheaf (Category.assoc f g s)) =
      (Scheme.Modules.pullback f).map (cotangentMap g s) ≫
        cotangentMap f (g ≫ s) := by
  apply (cancel_epi ((Scheme.Modules.pullbackComp f g).inv.app
    (cotangentSheaf s))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv _ _).injective
  apply ((cotangentPresentation s).universal _).1
  apply Construction.Lines.FamilyVariation.relativeDerivation_ext
  intro U a
  change (eqToHom (congrArg cotangentSheaf (Category.assoc f g s))).app
      ((f ≫ g) ⁻¹ᵁ U)
      ((cotangentMap (f ≫ g) s).app ((f ≫ g) ⁻¹ᵁ U)
        (pullLocalSection (f ≫ g) (cotangentSheaf s) U
          ((cotangentPresentation s).differential.apply U a))) =
    (cotangentMap f (g ≫ s)).app ((f ≫ g) ⁻¹ᵁ U)
      (((Scheme.Modules.pullback f).map (cotangentMap g s)).app ((f ≫ g) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackComp f g).inv.app (cotangentSheaf s)).app
          ((f ≫ g) ⁻¹ᵁ U)
          (pullLocalSection (f ≫ g) (cotangentSheaf s) U
            ((cotangentPresentation s).differential.apply U a))))
  rw [ContactDerivativeIsoProof.cotangentMap_differential,
    ContactDerivativeIsoProof.differential_transport _ _ (Category.assoc f g s),
    ExternalExchangeCoherenceProof.pullLocalSection_comp_inv]
  simp only [Scheme.Hom.comp_preimage]
  rw [ExternalExchangeCoherenceProof.pullLocalSection_map,
    ContactDerivativeIsoProof.cotangentMap_differential,
    ContactDerivativeIsoProof.cotangentMap_differential]
  rfl

/-- Pulling a normalized chart functional through the original source
cotangent map gives the functional on the common composite chart. -/
theorem composition_functional {X Y Z S : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : Y ⟶ Z) (s : Z ⟶ S)
    (q : cotangentSheaf (g ≫ s) ⟶ structureModule Y) :
    (Scheme.Modules.pullbackComp f g).inv.app (cotangentSheaf s) ≫
        (Scheme.Modules.pullback f).map (cotangentMap g s ≫ q) ≫
        unitPullbackMap f =
      cotangentMap (f ≫ g) s ≫
        pullAlong f (g ≫ s) ((f ≫ g) ≫ s) (Category.assoc f g s).symm q := by
  letI := openImmersion_cotangentMap_isIso f (g ≫ s)
  have hc := cotangentMap_comp f g s
  have hc' := congrArg (fun k =>
    (Scheme.Modules.pullbackComp f g).inv.app (cotangentSheaf s) ≫ k ≫
      (asIso (cotangentMap f (g ≫ s))).inv) hc
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
    asIso_inv, IsIso.hom_inv_id, Category.comp_id] at hc'
  have hh := congrArg (fun a => a ≫ (Scheme.Modules.pullback f).map q ≫
    unitPullbackMap f) hc'.symm
  simpa only [Functor.map_comp, Category.assoc, pullAlong, pull, asIso_inv] using hh


def derivation {T Y S : Scheme} (f : T ⟶ Y) [IsOpenImmersion f]
    (s : Y ⟶ S) (t : T ⟶ S) (h : f ≫ s = t)
    (q : cotangentSheaf s ⟶ structureModule Y) : RelativeSheafDerivation t (structureModule T) :=
  (cotangentPresentation t).differential.postcompose (pullAlong f s t h q)

theorem derivation_one {T S : Scheme} (t : T ⟶ S)
    (D : RelativeSheafDerivation t (structureModule T)) : D.apply ⊤ 1 = 0 := by
  have h := D.leibniz ⊤ (1 : RingSections T ⊤) 1
  simp only [one_mul, one_smul] at h
  have hh : D.apply ⊤ 1 + D.apply ⊤ 1 = D.apply ⊤ 1 + 0 := by
    simpa only [add_zero] using h.symm
  exact add_left_cancel hh

end LeBrunSalamon.OpenCotangentScalar
end
