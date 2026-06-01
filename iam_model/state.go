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

type IdentityPolicyAttachment struct {
	Identity IdentityID
	Policy   PolicyID
}

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
	mu            sync.Mutex
	identities    map[IdentityID]struct{}
	policies      map[PolicyID]IdentityPolicy
	attachments   map[IdentityPolicyAttachment]struct{}
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
		identities:    make(map[IdentityID]struct{}),
		policies:      make(map[PolicyID]IdentityPolicy),
		attachments:   make(map[IdentityPolicyAttachment]struct{}),
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
	s.identities[id] = struct{}{}
	return nil
}

// ListIdentities returns every identity known to this model.
// AWS SDK analogue: ListUsers; this model has only one identity kind.
func (s *State) ListIdentities() []IdentityID {
	s.mu.Lock()
	defer s.mu.Unlock()

	identities := make([]IdentityID, 0, len(s.identities))
	for identity := range s.identities {
		identities = append(identities, identity)
	}
	return identities
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

func (s *State) generateNewPolicyIDAndUpdate() PolicyID {
	for {
		id := PolicyID(fmt.Sprintf("policy-%d", rand.Int63()))
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

	if _, exists := s.identities[identity]; !exists {
		return fmt.Errorf("%w: identity %q", ErrNotFound, identity)
	}
	if _, exists := s.policies[policyID]; !exists {
		return fmt.Errorf("%w: policy %q", ErrNotFound, policyID)
	}

	attachment := IdentityPolicyAttachment{Identity: identity, Policy: policyID}
	if _, exists := s.attachments[attachment]; exists {
		return nil
	}
	s.attachments[attachment] = struct{}{}
	return nil
}

// ListIdentityPolicies returns policy IDs attached directly to identity.
// AWS SDK analogue: ListAttachedUserPolicies.
func (s *State) ListIdentityPolicies(identity IdentityID) ([]PolicyID, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	if _, exists := s.identities[identity]; !exists {
		return nil, fmt.Errorf("%w: identity %q", ErrNotFound, identity)
	}

	policies := make([]PolicyID, 0)
	for attachment := range s.attachments {
		if attachment.Identity == identity {
			policies = append(policies, attachment.Policy)
		}
	}
	return policies, nil
}

// GetIdentityPolicy returns the simplified attached policy object for id.
// AWS SDK analogue: GetPolicy followed by GetPolicyVersion.
func (s *State) GetIdentityPolicy(id PolicyID) (IdentityPolicy, error) {
	s.mu.Lock()
	defer s.mu.Unlock()

	policy, exists := s.policies[id]
	if !exists {
		return IdentityPolicy{}, fmt.Errorf("%w: policy %q", ErrNotFound, id)
	}
	return policy, nil
}

// DetachIdentityPolicy detaches a policy from an identity without deleting the policy.
// AWS SDK analogue: DetachUserPolicy.
func (s *State) DetachIdentityPolicy(identity IdentityID, policyID PolicyID) error {
	s.mu.Lock()
	defer s.mu.Unlock()

	if _, exists := s.identities[identity]; !exists {
		return fmt.Errorf("%w: identity %q", ErrNotFound, identity)
	}
	if _, exists := s.policies[policyID]; !exists {
		return fmt.Errorf("%w: policy %q", ErrNotFound, policyID)
	}

	attachment := IdentityPolicyAttachment{Identity: identity, Policy: policyID}
	if _, exists := s.attachments[attachment]; !exists {
		return fmt.Errorf("%w: identity policy attachment %q -> %q", ErrNotFound, identity, policyID)
	}
	delete(s.attachments, attachment)
	return nil
}
