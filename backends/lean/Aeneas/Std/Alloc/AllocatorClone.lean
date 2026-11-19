/- `core::alloc::AllocatorClone`: the marker trait required by the `alloc` collections whose
allocator is cloned (`BTreeMap`, `Rc`, ...). Allocators are not modelled: the only allocator is
`alloc::alloc::Global`. -/
module
public import Aeneas.Std.Alloc.Alloc
public section

namespace Aeneas.Std

@[rust_trait "core::alloc::AllocatorClone" (parentClauses := ["cloneCloneInst"])]
structure core.alloc.AllocatorClone (Self : Type _) where
  cloneCloneInst : core.clone.Clone Self

@[expose, reducible, rust_trait_impl "core::alloc::AllocatorClone<alloc::alloc::Global>"]
def core.alloc.AllocatorCloneGlobal : core.alloc.AllocatorClone alloc.alloc.Global := {
  cloneCloneInst := core.clone.CloneGlobal
}

end Aeneas.Std
