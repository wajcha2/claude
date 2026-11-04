import RecompileSections

/-! Composition and inversion of actual scheme isomorphisms over a base
which retain a specified line bundle. These small proofs keep the final
normal-form assembly from expanding long pullback comparison terms. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeBrunSalamon.PhaseOne LeBrunSalamon.PhaseTwo LeBrunSalamon.PhaseThree
open LeBrunSalamon.PhaseTwentyFive LeBrunSalamon.PhaseTwentySix
open LeBrunSalamon.PhaseTwentyEight

namespace LeBrunSalamon

structure PolarizedOverIso {X Y S : Scheme.{0}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (L : LineBundle X) (M : LineBundle Y) where
  iso : X ≅ Y
  over_base : iso.hom ≫ sY = sX
  lineIso : L.sheaf ≅ pullbackModule iso.hom M.sheaf

namespace PolarizedOverIso

variable {X Y Z S : Scheme.{0}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
  {L : LineBundle X} {M : LineBundle Y} {N : LineBundle Z}

def symm (e : PolarizedOverIso sX sY L M) : PolarizedOverIso sY sX M L where
  iso := e.iso.symm
  over_base := by
    calc
      e.iso.inv ≫ sX = e.iso.inv ≫ (e.iso.hom ≫ sY) :=
        congrArg (fun f : X ⟶ S => e.iso.inv ≫ f) e.over_base.symm
      _ = sY := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  lineIso :=
    (((Scheme.Modules.pullbackComp e.iso.inv e.iso.hom).app M.sheaf) ≪≫
      ((Scheme.Modules.pullbackCongr e.iso.inv_hom_id).app M.sheaf) ≪≫
      ((Scheme.Modules.pullbackId Y).app M.sheaf)).symm ≪≫
        (Scheme.Modules.pullback e.iso.inv).mapIso e.lineIso.symm

def trans (e : PolarizedOverIso sX sY L M) (f : PolarizedOverIso sY sZ M N) :
    PolarizedOverIso sX sZ L N where
  iso := e.iso ≪≫ f.iso
  over_base := by
    change (e.iso.hom ≫ f.iso.hom) ≫ sZ = sX
    rw [Category.assoc, f.over_base, e.over_base]
  lineIso := e.lineIso ≪≫ (Scheme.Modules.pullback e.iso.hom).mapIso f.lineIso ≪≫
    (Scheme.Modules.pullbackComp e.iso.hom f.iso.hom).app N.sheaf

theorem exists_iso (e : PolarizedOverIso sX sY L M) :
    ∃ f : X ≅ Y, f.hom ≫ sY = sX ∧ Nonempty (L.sheaf ≅ pullbackModule f.hom M.sheaf) :=
  ⟨e.iso, e.over_base, ⟨e.lineIso⟩⟩

end PolarizedOverIso
end LeBrunSalamon
end
