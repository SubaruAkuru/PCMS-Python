import Lake
open Lake DSL

package «pcms» where
  leanOptions := #[⟨`autoImplicit, false⟩]

@[default_target]
lean_lib «PCMS» where
