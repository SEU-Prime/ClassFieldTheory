import Mathlib
open
  CategoryTheory
  Limits
  groupCohomology
  groupHomology
  Rep
  LinearMap

variable {R : Type} [CommRing R]
variable {G : Type} [Group G] [Finite G]

noncomputable section

namespace Representation
variable {A : Type} [AddCommGroup A] [Module R A] (ρ : Representation R G A)

def norm : A →ₗ[R] A :=
  let _ := Fintype.ofFinite G
  ∑ g : G, ρ g

lemma norm_comm (g : G) : ρ g ∘ₗ ρ.norm = ρ.norm :=by
  ext s

  simp only [norm,LinearMap.coe_comp, coeFn_sum,
   Function.comp_apply, Finset.sum_apply, map_sum,←Module.End.mul_apply,←map_mul]
--
  refine Finset.sum_equiv ⟨fun n↦g*n,fun n↦ g⁻¹*n,fun _ ↦ by simp only [inv_mul_cancel_left] ,
fun _ ↦ by simp only [mul_inv_cancel_left]⟩ (fun i ↦ by simp only [Finset.mem_univ, Equiv.coe_fn_mk]) (fun i hi↦ by
   simp only [map_mul, Module.End.mul_apply, Equiv.coe_fn_mk] )





lemma norm_comm' (g : G) : ρ.norm ∘ₗ ρ g = ρ.norm :=by
  ext s
  simp only [norm, LinearMap.coe_comp, coeFn_sum, Function.comp_apply, Finset.sum_apply,
  ←Module.End.mul_apply,←map_mul]

  refine Finset.sum_equiv (⟨fun n↦n*g,fun n↦ n*g⁻¹,fun _ ↦ by simp only [mul_inv_cancel_right],
fun _ ↦ by simp only [inv_mul_cancel_right]⟩) (fun i ↦ by simp only [Finset.mem_univ, Equiv.coe_fn_mk]) (fun i hi↦ by
   simp only [map_mul, Module.End.mul_apply, Equiv.coe_fn_mk])



end Representation

namespace groupCohomology

variable[DecidableEq G]

def _root_.groupHomology.zeroChainsIso (M : Rep R G) : (inhomogeneousChains M).X 0 ≅ M.V :=
  LinearEquiv.toModuleIso (Finsupp.LinearEquiv.finsuppUnique R (↑M.V) (Fin 0 → G))

def _root_.Rep.norm (M : Rep R G) : M.V ⟶ M.V := ModuleCat.ofHom M.ρ.norm

/--
This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`.
-/
def TateNorm (M : Rep R G) : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (zeroChainsIso M).hom ≫ M.norm ≫ (cochainsIso₀ M).inv

lemma TateNorm_comp_d (M : Rep R G) : TateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 :=by
  ext s hs v
  have : (0 : ↑(ModuleCat.of R ((Fin 1 → G) → ↑M.V))) v = 0 := by rfl
  simpa [TateNorm, Rep.norm,Representation.norm,zero_apply,cochainsIso₁,zeroChainsIso,this,
  ← Module.End.mul_apply,←map_mul]
  using sub_eq_zero.mpr (Finset.sum_equiv  ⟨fun n ↦ (v 0) * n,fun n ↦ (v 0)⁻¹ * n,fun _ ↦ by simp only [inv_mul_cancel_left],
fun _ ↦ by simp only [mul_inv_cancel_left]⟩ (fun i ↦ by simp only [Finset.mem_univ, Fin.isValue, Equiv.coe_fn_mk])
    (fun i hi ↦ by simp only [Fin.isValue, map_mul, Module.End.mul_apply, Equiv.coe_fn_mk]))






lemma d_comp_TateNorm (M : Rep R G) : (inhomogeneousChains M).d 1 0 ≫ TateNorm M  = 0 :=by
  ext s hs v
  have:(0:↑(ModuleCat.of R ((Fin 0 → G) → ↑M.V))) v=0 :=by rfl
  simpa [ModuleCat.of_coe, CochainComplex.of_x, ChainComplex.of, inhomogeneousChains.d,
    zero_add, ↓reduceDIte, TateNorm, zeroChainsIso,Rep.norm, Representation.norm, cochainsIso₀,
    this,← sub_eq_add_neg]
  using sub_eq_zero.mpr (Finset.sum_equiv ⟨fun n ↦ n * (s 0)⁻¹ ,fun n ↦n * (s 0),fun _ ↦by simp,
fun _ ↦ by simp⟩ (fun i  ↦  by simp) (fun i hi ↦ (  by
  have l1:((fun₀ | fun (i : Fin 0) ↦ s (i.succ) => (M.ρ (s 0)⁻¹) hs) default) =(M.ρ (s 0)⁻¹)  hs :=by
    simp only [Finsupp.single, Fin.isValue, Finsupp.coe_mk,Pi.single, Function.update]
    refine dite_eq_iff.mpr ( Or.symm (Or.inr (Exists.of_psigma_prop (by
     simpa using  ⟨List.ofFn_inj.mp rfl, by simp⟩))))
  have l2: ((fun₀ | Fin.contractNth 0 (fun x1 x2 ↦ x1 * x2) s => hs) default)= hs :=by
     have:default = Fin.contractNth 0 (fun x1 x2 ↦ x1 * x2) s :=List.ofFn_inj.mp rfl
     simp only [ModuleCat.of_coe, Finsupp.single, Fin.isValue, Pi.single, this, Finsupp.coe_mk,
       Function.update, ↓reduceDIte]
  simp only [Fin.isValue, l1, Equiv.coe_fn_mk, map_mul, l2, Module.End.mul_apply]

)
))



def TateComplex.ConnectData (M : Rep R G) :
    CochainComplex.ConnectData (inhomogeneousChains M) (inhomogeneousCochains M) where
  d₀ := TateNorm M
  comp_d₀ := d_comp_TateNorm M
  d₀_comp := TateNorm_comp_d M

def TateComplex (M : Rep R G) : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.ConnectData.cochainComplex (TateComplex.ConnectData M)

lemma TateComplex_d_neg_one (M : Rep R G) : (TateComplex M).d (-1) 0 = TateNorm M := rfl

lemma TateComplex_d_ofNat (M : Rep R G) (n : ℕ) :
    (TateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl

lemma TateComplex_d_neg (M : Rep R G) (n : ℕ) :
    (TateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

def TateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := TateComplex M
  map φ := {
    f
    | Int.ofNat i => ((cochainsFunctor R G).map φ).f ↑i
    | Int.negSucc i => (chainsMap (MonoidHom.id G) φ).f i
    comm' i j sij :=by
      simp only [ComplexShape.up_Rel] at sij
      simp only [cochainsFunctor_obj, cochainsFunctor_map, cochainsMap, Action.res_obj_V,
        MonoidHom.coe_id, CompTriple.comp_eq, ModuleCat.ofHom_comp]
      
      sorry

  }
  map_id := sorry
  map_comp := sorry

def TateCohomology (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  TateComplexFunctor ⋙ HomologicalComplex.homologyFunctor _ _ n

/-
The next two statements say that `TateComplexFunctor` is an exact functor.
-/
instance TateComplexFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

instance TateComplexFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (TateComplexFunctor (R := R) (G := G)) :=
  sorry

lemma TateCohomology.cochainsFunctor_Exact {S : ShortComplex (Rep R G)}
    (hS : S.ShortExact) : (S.map TateComplexFunctor).ShortExact :=
  ShortComplex.ShortExact.map_of_exact hS TateComplexFunctor

/--
The connecting homomorphism in group cohomology induced by a short exact sequence of `G`-modules.
-/
noncomputable abbrev TateCohomology.δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact)
    (n : ℤ) : (TateCohomology n).obj S.X₃ ⟶ (TateCohomology (n + 1)).obj S.X₁ :=
  (TateCohomology.cochainsFunctor_Exact hS).δ n (n + 1) rfl

def TateCohomology.iso_groupCohomology (n : ℕ) (M : Rep R G) :
    TateCohomology (n + 1) ≅ groupCohomology.functor R G (n + 1) := by
  convert Iso.refl _
  sorry

def TateCohomology.iso_groupHomology (n : ℕ) (M : Rep R G) :
    (TateCohomology (-n - 2)).obj M ≅ groupHomology M (n + 1) := by
  convert Iso.refl _
  sorry

def TateCohomology_zero_iso (M : Rep R G) : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.ρ.invariants ⧸ (range M.ρ.norm).submoduleOf M.ρ.invariants) :=
  sorry

def TateCohomology_neg_one_iso (M : Rep R G) : (TateCohomology (-1)).obj M ≅
    ModuleCat.of R (ker M.ρ.norm ⧸
    (Submodule.span R (⋃ g : G, range (1 - M.ρ g))).submoduleOf (ker M.ρ.norm)) :=
  sorry

def TateCohomology_zero_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] : (TateCohomology 0).obj M ≅
    ModuleCat.of R (M.V ⧸ (range (Nat.card G : M.V →ₗ[R] M.V))) :=
  sorry

def TateCohomology_neg_one_iso_of_isTrivial (M : Rep R G) [M.ρ.IsTrivial] :
    (TateCohomology (-1)).obj M ≅ ModuleCat.of R (ker (Nat.card G : M.V →ₗ[R] M.V)):=
  sorry

end groupCohomology
end
