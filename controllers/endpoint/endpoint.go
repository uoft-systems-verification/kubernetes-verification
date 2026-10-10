package endpoint

import (
	"kubernetes_model/apimodel"

	v1 "k8s.io/api/core/v1"
	"k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/labels"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/apimachinery/pkg/util/intstr"
)

func podReady(pod *v1.Pod) bool {
	for _, condition := range pod.Status.Conditions {
		if condition.Type == v1.PodReady && condition.Status == v1.ConditionTrue {
			return true
		}
	}
	return false
}

// targetPort resolves a ServicePort to the port that a selected Pod serves.
// An omitted targetPort defaults to the Service port; a named targetPort is
// looked up in the Pod's container ports.
func targetPort(pod *v1.Pod, servicePort *v1.ServicePort) (int32, bool) {
	switch servicePort.TargetPort.Type {
	case intstr.String:
		for _, container := range pod.Spec.Containers {
			for _, port := range container.Ports {
				if port.Name == servicePort.TargetPort.StrVal && port.Protocol == servicePort.Protocol {
					return port.ContainerPort, true
				}
			}
		}
		return 0, false
	case intstr.Int:
		if port := servicePort.TargetPort.IntVal; port != 0 {
			return port, true
		}
		return servicePort.Port, true
	default:
		return servicePort.Port, true
	}
}

func buildEndpoints(service *v1.Service, pods []*v1.Pod) *v1.Endpoints {
	result := &v1.Endpoints{
		ObjectMeta: metav1.ObjectMeta{
			Name:      service.Name,
			Namespace: service.Namespace,
			Labels:    service.Labels,
		},
	}

	for _, pod := range pods {
		if pod.DeletionTimestamp != nil || pod.Status.PodIP == "" {
			continue
		}

		address := v1.EndpointAddress{
			IP: pod.Status.PodIP,
			TargetRef: &v1.ObjectReference{
				Kind:      "Pod",
				Name:      pod.Name,
				Namespace: pod.Namespace,
				UID:       pod.UID,
			},
		}
		subset := v1.EndpointSubset{Ports: make([]v1.EndpointPort, 0, len(service.Spec.Ports))}
		for i := range service.Spec.Ports {
			servicePort := &service.Spec.Ports[i]
			port, found := targetPort(pod, servicePort)
			if !found {
				continue
			}
			subset.Ports = append(subset.Ports, v1.EndpointPort{
				Name:        servicePort.Name,
				Port:        port,
				Protocol:    servicePort.Protocol,
				AppProtocol: servicePort.AppProtocol,
			})
		}

		if len(service.Spec.Ports) > 0 && len(subset.Ports) == 0 {
			continue
		}
		if service.Spec.PublishNotReadyAddresses || podReady(pod) {
			subset.Addresses = []v1.EndpointAddress{address}
		} else {
			subset.NotReadyAddresses = []v1.EndpointAddress{address}
		}
		result.Subsets = append(result.Subsets, subset)
	}
	return result
}

func syncEndpoints(namespace, name string) error {
	service, err := apimodel.ModelState.ServiceGet(namespace, name)
	if errors.IsNotFound(err) {
		return nil
	}
	if err != nil {
		return err
	}
	if service.Spec.Selector == nil {
		return nil
	}

	selector := labels.Set(service.Spec.Selector).AsSelectorPreValidated()
	pods, err := apimodel.ModelState.PodList(namespace, selector)
	if err != nil {
		return err
	}

	endpoints := buildEndpoints(service, pods)
	current, err := apimodel.ModelState.EndpointsGet(namespace, name)
	if errors.IsNotFound(err) {
		_, err = apimodel.ModelState.EndpointsCreate(namespace, endpoints)
		return err
	}
	if err != nil {
		return err
	}

	endpoints.ResourceVersion = current.ResourceVersion
	_, err = apimodel.ModelState.EndpointsUpdate(namespace, endpoints)
	return err
}
