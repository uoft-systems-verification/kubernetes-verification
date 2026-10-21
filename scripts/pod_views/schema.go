//go:build ignore

// Run from the Kubernetes module; this helper is not a package of the root
// tooling module.
package main

import (
	"encoding/json"
	"os"
	"reflect"

	corev1 "k8s.io/api/core/v1"
)

type node struct {
	ID     string
	Name   string
	Pkg    string
	Kind   string
	Elem   string
	Key    string
	Fields []field
}
type field struct {
	Name string
	Type string
}

func main() {
	nodes := map[string]node{}
	var order []string
	var visit func(reflect.Type) string
	visit = func(t reflect.Type) string {
		id := t.String()
		if t.Name() != "" {
			id = t.PkgPath() + "/" + t.Name()
		}
		if _, ok := nodes[id]; ok {
			return id
		}
		n := node{ID: id, Name: t.Name(), Pkg: t.PkgPath(), Kind: t.Kind().String()}
		nodes[id] = n
		switch t.Kind() {
		case reflect.Pointer, reflect.Slice, reflect.Array:
			n.Elem = visit(t.Elem())
		case reflect.Map:
			n.Key = visit(t.Key())
			n.Elem = visit(t.Elem())
		case reflect.Struct:
			if t.PkgPath() == "k8s.io/apimachinery/pkg/apis/meta/v1" && (t.Name() == "Time" || t.Name() == "ObjectMeta") {
				break
			}
			for i := 0; i < t.NumField(); i++ {
				f := t.Field(i)
				n.Fields = append(n.Fields, field{f.Name, visit(f.Type)})
			}
		}
		nodes[id] = n
		order = append(order, id)
		return id
	}
	visit(reflect.TypeOf(corev1.PodSpec{}))
	visit(reflect.TypeOf(corev1.PodStatus{}))
	out := struct {
		Nodes map[string]node
		Order []string
	}{nodes, order}
	json.NewEncoder(os.Stdout).Encode(out)
}
