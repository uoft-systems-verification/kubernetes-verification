// Package iammodel is a small IAM-style model for attached identity policies.
//
// The model keeps only one identity kind and one resource-name kind. Policies
// are first-class objects attached to identities, and every policy is an Allow
// policy for one resource name. There are no inline policies, deny policies,
// resource-based policies, actions, conditions, groups, roles, or resource
// objects.
package iammodel

import (
	"errors"
	"fmt"
	"math/rand"
	"sync"
)

type IdentityID string
type ResourceName string
type PolicyID string

// IdentityPolicy is a simplified identity-based Allow policy.
//
// The real IAM policy document is collapsed to one resource name. All policies
// are Allow policies. The identity is not part of the policy document; access is
// granted by attaching the policy to an identity.
type IdentityPolicy struct {
	ID PolicyID

	Resource ResourceName
}

// State stores the whole local IAM model.
//
// usedPolicyIds remembers every generated policy ID, so generated policy IDs
// are never reused.
type State struct {
	mu            *sync.Mutex
	identities    map[IdentityID]map[PolicyID]struct{}
	policies      map[PolicyID]IdentityPolicy
	usedPolicyIds map[PolicyID]struct{}
}

var (
	ErrInvalidID     = errors.New("invalid id")
	ErrAlreadyExists = errors.New("already exists")
	ErrNotFound      = errors.New("not found")
)

var ModelState = NewState()

func NewState() *State {
	return &State{
		mu:            new(sync.Mutex),
		identities:    make(map[IdentityID]map[PolicyID]struct{}),
		policies:      make(map[PolicyID]IdentityPolicy),
		usedPolicyIds: make(map[PolicyID]struct{}),
	}
}

// CreateIdentity adds an IAM identity.
// AWS SDK analogue: CreateUser; this model collapses all identity kinds.
func (s *State) CreateIdentity(id IdentityID) error {
	if id == "" {
		return fmt.Errorf("%w: empty identity id", ErrInvalidID)
	}

	s.mu.Lock()
	defer s.mu.Unlock()

	if _, exists := s.identities[id]; exists {
		return fmt.Errorf("%w: identity %q", ErrAlreadyExists, id)
	}
	s.identities[id] = make(map[PolicyID]struct{})
	return nil
}

// Snapshot returns copies of the identity attachment map and the policy
// document map.
func (s *State) Snapshot() (map[IdentityID]map[PolicyID]struct{}, map[PolicyID]IdentityPolicy) {
	s.mu.Lock()
	defer s.mu.Unlock()

	return copyIdentities(s.identities), copyPolicies(s.policies)
}

func copyIdentities(src map[IdentityID]map[PolicyID]struct{}) map[IdentityID]map[PolicyID]struct{} {
	identities := make(map[IdentityID]map[PolicyID]struct{})
	for identity, policyIDs := range src {
		policyIDsCopy := make(map[PolicyID]struct{})
		for policyID := range policyIDs {
			policyIDsCopy[policyID] = struct{}{}
		}
		identities[identity] = policyIDsCopy
	}
	return identities
}

func copyPolicies(src map[PolicyID]IdentityPolicy) map[PolicyID]IdentityPolicy {
	policies := make(map[PolicyID]IdentityPolicy)
	for policyID, policy := range src {
		policies[policyID] = policy
	}
	return policies
}

// CreatePolicy creates a standalone identity-based Allow policy document.
// AWS SDK analogue: CreatePolicy.
func (s *State) CreatePolicy(resource ResourceName) (PolicyID, error) {
	if resource == "" {
		return "", fmt.Errorf("%w: empty resource name", ErrInvalidID)
	}

	s.mu.Lock()
	defer s.mu.Unlock()

	id := s.generateNewPolicyIDAndUpdate()
	s.policies[id] = IdentityPolicy{
		ID:       id,
		Resource: resource,
	}
	return id, nil
}

func generatePolicyID() PolicyID {
	return PolicyID(fmt.Sprintf("policy-%d", rand.Int63()))
}

func (s *State) generateNewPolicyIDAndUpdate() PolicyID {
	for {
		id := generatePolicyID()
		if _, exists := s.usedPolicyIds[id]; !exists {
			s.usedPolicyIds[id] = struct{}{}
			return id
		}
	}
}

// AttachIdentityPolicy attaches an existing policy to an identity.
// AWS SDK analogue: AttachUserPolicy.
func (s *State) AttachIdentityPolicy(identity IdentityID, policyID PolicyID) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	policyIDs, exists := s.identities[identity]
	if !exists {
		return fmt.Errorf("%w: identity %q", ErrNotFound, identity)
	}
	if _, exists = s.policies[policyID]; !exists {
		return fmt.Errorf("%w: policy %q", ErrNotFound, policyID)
	}

	if _, exists = policyIDs[policyID]; exists {
		return nil
	}
	policyIDs[policyID] = struct{}{}
	return nil
}

// DetachIdentityPolicy detaches a policy from an identity without deleting the policy.
// AWS SDK analogue: DetachUserPolicy.
func (s *State) DetachIdentityPolicy(identity IdentityID, policyID PolicyID) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	policyIDs, exists := s.identities[identity]
	if !exists {
		return fmt.Errorf("%w: identity %q", ErrNotFound, identity)
	}
	if _, exists = s.policies[policyID]; !exists {
		return fmt.Errorf("%w: policy %q", ErrNotFound, policyID)
	}

	if _, exists = policyIDs[policyID]; !exists {
		return fmt.Errorf("%w: identity policy attachment %q -> %q", ErrNotFound, identity, policyID)
	}
	delete(policyIDs, policyID)
	return nil
}
