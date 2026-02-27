package apimodel

import (
	"k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/runtime/schema"
)

func (s *State) get(key KKey) (interface{}, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	item, exists := s.m[key]
	if exists {
		return deepCopy(item), nil
	} else {
		return nil, errors.NewNotFound(schema.GroupResource{Resource: key.Kind}, key.Name)
	}
}
