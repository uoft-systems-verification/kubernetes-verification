From New.proof Require Import prelude empty_ffi.

Class top_level (Σ : gFunctors) (V : Type) := {
  (* update_meta and update_spec are the views of the existing object's
    metadata and spec used to validate an update request. *)
  update_meta : Type;
  update_spec : Type;
  status_update_status : Type;
  (* valid describes the conditions that hold on a k8s object stored in etcd. *)
  valid : V → Prop;
  (* extra_valid describes extra conditions that are not enforced by k8s but
    very unlikely to not hold in reality. They are global assumptions of the k8s cluster. *)
  extra_valid : V → Prop;
  (* valid_create takes the request kind and namespace and the object submitted
    to the create request. It states that the request won't fail because of
    those inputs. *)
  valid_create : go_string → go_string → V → Prop;
  (* valid_update takes the request kind and namespace, the metadata and spec
    currently stored in etcd, and the object submitted to the update request.
    It states that the request won't fail because of those inputs. *)
  valid_update : go_string → go_string → update_meta → update_spec → V → Prop;
  (* valid_status_update takes the request kind and namespace, the metadata
    and status currently stored in etcd, and the submitted object. *)
  valid_status_update :
    go_string → go_string → update_meta → status_update_status → V → Prop;
  (* created takes the namespace and the object that are input to the create request,
    and also the resulting new object stored in etcd, and then states whether the resulting object is the correct
    object created from the input, e.g., whether some fields from the stored object are the same as the input one,
    or the same as after normalization/defaulting. *)
  created : go_string → V → V → Prop;
  (* updated relates the object submitted to the update request to the object
    stored after a successful update. It does not constrain the stored status. *)
  updated : V → V → Prop;
  (* status_updated relates the object submitted to the status update request
    to the object stored after a successful status update. It does not
    constrain the stored spec. *)
  status_updated : V → V → Prop;
  (* deepown_l relates the view object to the Go object using a pointer. *)
  deepown_l : loc → V → dfrac → iProp Σ;
}.
