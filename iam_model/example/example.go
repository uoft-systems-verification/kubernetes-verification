package example

import iammodel "iam_model"

// ReconcileIdentityAccess ensures that the identity-based policies for resource
// grant access to exactly the identities in desired.
func ReconcileIdentityAccess(desired map[iammodel.IdentityID]struct{}, resource iammodel.ResourceName) error {
	identities, policies := iammodel.ModelState.Snapshot()
	current := identitiesWithPolicyForResource(identities, policies, resource)

	for _, identity := range current {
		if _, keep := desired[identity]; keep {
			continue
		}
		policyIDs := policiesForResource(identities, policies, identity, resource)
		for _, policyID := range policyIDs {
			if err := iammodel.ModelState.DetachIdentityPolicy(identity, policyID); err != nil {
				return err
			}
		}
	}

	missing := make([]iammodel.IdentityID, 0)
	for identity := range desired {
		if containsIdentity(current, identity) {
			continue
		}
		missing = append(missing, identity)
	}

	if len(missing) == 0 {
		return nil
	}

	policyID, err := iammodel.ModelState.CreatePolicy(resource)
	if err != nil {
		return err
	}
	for _, identity := range missing {
		if err := iammodel.ModelState.AttachIdentityPolicy(identity, policyID); err != nil {
			return err
		}
	}

	return nil
}

func identitiesWithPolicyForResource(
	identities map[iammodel.IdentityID]map[iammodel.PolicyID]struct{},
	policies map[iammodel.PolicyID]iammodel.IdentityPolicy,
	resource iammodel.ResourceName,
) []iammodel.IdentityID {
	matchingIdentities := make([]iammodel.IdentityID, 0)
	for identity, policyIDs := range identities {
		if hasPolicyForResource(policyIDs, policies, resource) {
			matchingIdentities = append(matchingIdentities, identity)
		}
	}
	return matchingIdentities
}

func hasPolicyForResource(
	policyIDs map[iammodel.PolicyID]struct{},
	policies map[iammodel.PolicyID]iammodel.IdentityPolicy,
	resource iammodel.ResourceName,
) bool {
	for policyID := range policyIDs {
		policy, exists := policies[policyID]
		if exists && policy.Resource == resource {
			return true
		}
	}
	return false
}

func policiesForResource(
	identities map[iammodel.IdentityID]map[iammodel.PolicyID]struct{},
	policies map[iammodel.PolicyID]iammodel.IdentityPolicy,
	identity iammodel.IdentityID,
	resource iammodel.ResourceName,
) []iammodel.PolicyID {
	matchingPolicyIDs := make([]iammodel.PolicyID, 0)
	for policyID := range identities[identity] {
		policy, exists := policies[policyID]
		if exists && policy.Resource == resource {
			matchingPolicyIDs = append(matchingPolicyIDs, policyID)
		}
	}
	return matchingPolicyIDs
}

func containsIdentity(identities []iammodel.IdentityID, target iammodel.IdentityID) bool {
	for _, identity := range identities {
		if identity == target {
			return true
		}
	}
	return false
}
