import RecompileExtensionsPart04Geometry

/-! A polarized plane conic is characterized by its actual quotient tuple
on all test schemes, including nonreduced test schemes. This file only proves
uniqueness and transport of such a presentation; it does not assume or assert
that a project family possesses one. That existence must be obtained from the
chosen-line embedding and its actual defining quadratic ideal. No admission. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight
open LeBrunSalamon.Skeleton LeBrunSalamon.Refinement

namespace LeBrunSalamon.PlaneConicPresentation

/-- The actual line-valued equation z₀z₁=δz₂², with the coefficient pulled
through the specified base morphism. -/
def Equation {S T : Scheme} (δ : RingSections S ⊤) (s : T ⟶ S)
    (L : LineBundle T) (a : Fin 3 → AlgebraicSection L.sheaf) : Prop :=
  tensorSection (a 0) (a 1) =
    sectionFromValue (s.appTop δ • sectionValue (tensorSection (a 2) (a 2)))

/-- A literal representing presentation of the displayed hypersurface,
including its chosen hyperplane line and all quotient coordinates. -/
structure Presentation (S : Scheme) (δ : RingSections S ⊤) where
  source : Scheme
  projection : source ⟶ S
  line : LineBundle source
  coordinate : Fin 3 → AlgebraicSection line.sheaf
  generates : TupleGenerates line coordinate
  equation : Equation δ projection line coordinate
  universal : ∀ (T : Scheme) (s : T ⟶ S) (L : LineBundle T)
    (a : Fin 3 → AlgebraicSection L.sheaf), TupleGenerates L a →
    Equation δ s L a →
      ∃! f : {f : T ⟶ source // f ≫ projection = s},
        ∃ e : pullbackModule f.val line.sheaf ≅ L.sheaf,
          ∀ i, pullSection f.val (coordinate i) ≫ e.hom = a i

/-- Change only the proof of the displayed coefficient identity.  All
geometric fields remain definitionally the original fields. -/
def reparameterize {S : Scheme} {δ δ' : RingSections S ⊤}
    (F : Presentation S δ) (h : δ = δ') : Presentation S δ' where
  source := F.source
  projection := F.projection
  line := F.line
  coordinate := F.coordinate
  generates := F.generates
  equation := by rw [← h]; exact F.equation
  universal := by
    intro T s L a ha heq
    apply F.universal T s L a ha
    rw [h]
    exact heq

variable {S : Scheme} {δ : RingSections S ⊤}

def mapPoint (F G : Presentation S δ) :
    {f : F.source ⟶ G.source // f ≫ G.projection = F.projection} :=
  Classical.choose (G.universal F.source F.projection F.line F.coordinate
    F.generates F.equation)

theorem mapPoint_spec (F G : Presentation S δ) :
    ∃ e : pullbackModule (mapPoint F G).val G.line.sheaf ≅ F.line.sheaf,
      ∀ i, pullSection (mapPoint F G).val (G.coordinate i) ≫ e.hom = F.coordinate i :=
  (Classical.choose_spec (G.universal F.source F.projection F.line F.coordinate
    F.generates F.equation)).1

def mapLine (F G : Presentation S δ) :
    pullbackModule (mapPoint F G).val G.line.sheaf ≅ F.line.sheaf :=
  Classical.choose (mapPoint_spec F G)

theorem mapLine_coordinate (F G : Presentation S δ) (i : Fin 3) :
    pullSection (mapPoint F G).val (G.coordinate i) ≫ (mapLine F G).hom =
      F.coordinate i := Classical.choose_spec (mapPoint_spec F G) i

/-- Coordinate-preserving maps between two representing hypersurfaces
compose to the identity. The chosen line comparison is retained explicitly. -/
theorem composite_identity (F G : Presentation S δ) :
    (mapPoint F G).val ≫ (mapPoint G F).val = 𝟙 F.source := by
  let f := (mapPoint F G).val
  let g := (mapPoint G F).val
  let p := (Scheme.Modules.pullbackComp f g).app F.line.sheaf
  let c : pullbackModule (f ≫ g) F.line.sheaf ≅ F.line.sheaf :=
    p.symm ≪≫ (Scheme.Modules.pullback f).mapIso (mapLine G F) ≪≫ mapLine F G
  have hc (i : Fin 3) :
      pullSection (f ≫ g) (F.coordinate i) ≫ c.hom = F.coordinate i := by
    calc
      _ = pullSection f
          (pullSection g (F.coordinate i) ≫ (mapLine G F).hom) ≫
            (mapLine F G).hom := by
        change pullSection (f ≫ g) (F.coordinate i) ≫
          (p.inv ≫ (Scheme.Modules.pullback f).map (mapLine G F).hom ≫
            (mapLine F G).hom) = _
        rw [← CanonicalPullbackSectionProof.pullSection_comp]
        change (pullSection f (pullSection g (F.coordinate i)) ≫ p.hom) ≫
          (p.inv ≫ (Scheme.Modules.pullback f).map (mapLine G F).hom ≫
            (mapLine F G).hom) = _
        simp only [Category.assoc, p.hom_inv_id_assoc]
        rw [ExternalExchangeCoherenceProof.pullSection_map, Category.assoc]
      _ = pullSection f (G.coordinate i) ≫ (mapLine F G).hom := by
        rw [mapLine_coordinate]
      _ = F.coordinate i := mapLine_coordinate F G i
  have hfg : (f ≫ g) ≫ F.projection = F.projection := by
    rw [Category.assoc, (mapPoint G F).property, (mapPoint F G).property]
  let fg : {a : F.source ⟶ F.source // a ≫ F.projection = F.projection} := ⟨f ≫ g, hfg⟩
  let idp : {a : F.source ⟶ F.source // a ≫ F.projection = F.projection} :=
    ⟨𝟙 F.source, Category.id_comp _⟩
  obtain ⟨a, _, hu⟩ := F.universal F.source F.projection F.line F.coordinate
    F.generates F.equation
  have h₁ : fg = a := hu fg ⟨c, hc⟩
  have h₂ : idp = a := hu idp
    ⟨(Scheme.Modules.pullbackId F.source).app F.line.sheaf,
      fun i => ExternalExchangeCoherenceProof.pullSection_id (F.coordinate i)⟩
  exact congrArg Subtype.val (h₁.trans h₂.symm)

def presentationIso (F G : Presentation S δ) : F.source ≅ G.source where
  hom := (mapPoint F G).val
  inv := (mapPoint G F).val
  hom_inv_id := composite_identity F G
  inv_hom_id := composite_identity G F

@[reassoc] theorem presentationIso_over (F G : Presentation S δ) :
    (presentationIso F G).hom ≫ G.projection = F.projection :=
  (mapPoint F G).property

/-- The isomorphism identifies the original selected polarization, with
the same actual pullback functor used in the target statement. -/
def presentationIso_line (F G : Presentation S δ) :
    F.line.sheaf ≅ pullbackModule (presentationIso F G).hom G.line.sheaf :=
  (mapLine F G).symm

end LeBrunSalamon.PlaneConicPresentation
end
