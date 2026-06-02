package example

import iammodel "iam_model"

// ReconcileIdentityAccess ensures that the identity-based policies for resource
// grant access to exactly the identities in desired.
func ReconcileIdentityAccess(desired map[iammodel.IdentityID]struct{}, resource iammodel.ResourceName) error {
	current, err := identitiesWithPolicyForResource(resource)
	if err != nil {
		return err
	}

	for _, identity := range current {
		if _, keep := desired[identity]; keep {
			continue
		}
		policyIDs, err := policiesForResource(identity, resource)
		if err != nil {
			return err
		}
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

func identitiesWithPolicyForResource(resource iammodel.ResourceName) ([]iammodel.IdentityID, error) {
	identities := make([]iammodel.IdentityID, 0)
	for _, identity := range iammodel.ModelState.ListIdentities() {
		hasPolicy, err := hasPolicyForResource(identity, resource)
		if err != nil {
			return nil, err
		}
		if hasPolicy {
			identities = append(identities, identity)
		}
	}
	return identities, nil
}

func hasPolicyForResource(identity iammodel.IdentityID, resource iammodel.ResourceName) (bool, error) {
	policyIDs, err := policiesForResource(identity, resource)
	if err != nil {
		return false, err
	}
	return len(policyIDs) != 0, nil
}

func policiesForResource(identity iammodel.IdentityID, resource iammodel.ResourceName) ([]iammodel.PolicyID, error) {
	policyIDs, err := iammodel.ModelState.ListIdentityPolicies(identity)
	if err != nil {
		return nil, err
	}
	matchingPolicyIDs := make([]iammodel.PolicyID, 0)
	for _, policyID := range policyIDs {
		policy, err := iammodel.ModelState.GetIdentityPolicy(policyID)
		if err != nil {
			return nil, err
		}
		if policy.Resource == resource {
			matchingPolicyIDs = append(matchingPolicyIDs, policyID)
		}
	}
	return matchingPolicyIDs, nil
}

func containsIdentity(identities []iammodel.IdentityID, target iammodel.IdentityID) bool {
	for _, identity := range identities {
		if identity == target {
			return true
		}
	}
	return false
}
