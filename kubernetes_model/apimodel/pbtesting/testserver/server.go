package testserver

import (
	"context"
	"fmt"
	"os"
	"path/filepath"

	appsv1 "k8s.io/api/apps/v1"
	corev1 "k8s.io/api/core/v1"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	"k8s.io/client-go/kubernetes"
	"k8s.io/client-go/rest"
	"k8s.io/client-go/tools/clientcmd"
	"sigs.k8s.io/controller-runtime/pkg/envtest"
)

// TestServer wraps a Kubernetes API server for testing.
type TestServer struct {
	client    kubernetes.Interface
	config    *rest.Config
	namespace string
	testEnv   *envtest.Environment // nil if using external cluster
}

// Config holds configuration for the test server.
type Config struct {
	// Namespace to use for tests (will be created if it doesn't exist).
	Namespace string

	// UseExternalCluster uses KUBECONFIG instead of envtest.
	// If false (default), uses envtest to start a local API server + etcd.
	UseExternalCluster bool
}

// NewTestServer creates a new test server.
// By default, it uses envtest to start a local API server + etcd (no controllers).
// Set UseExternalCluster=true to use an existing cluster via KUBECONFIG.
func NewTestServer(cfg Config) (*TestServer, error) {
	namespace := cfg.Namespace
	if namespace == "" {
		namespace = "pbt"
	}

	var config *rest.Config
	var testEnv *envtest.Environment
	var err error

	if cfg.UseExternalCluster {
		config, err = getExternalClusterConfig()
		if err != nil {
			return nil, fmt.Errorf("failed to get external cluster config: %w", err)
		}
	} else {
		testEnv = &envtest.Environment{
			// ErrorIfCRDPathMissing: false, // We don't need CRDs for core resources
		}

		config, err = testEnv.Start()
		if err != nil {
			return nil, fmt.Errorf("failed to start envtest: %w", err)
		}
	}

	client, err := kubernetes.NewForConfig(config)
	if err != nil {
		if testEnv != nil {
			_ = testEnv.Stop()
		}
		return nil, fmt.Errorf("failed to create client: %w", err)
	}

	server := &TestServer{
		client:    client,
		config:    config,
		namespace: namespace,
		testEnv:   testEnv,
	}

	// Ensure namespace exists
	if err := server.ensureNamespace(context.Background()); err != nil {
		server.Stop()
		return nil, fmt.Errorf("failed to ensure namespace: %w", err)
	}

	return server, nil
}

// getExternalClusterConfig gets config from KUBECONFIG or default location.
func getExternalClusterConfig() (*rest.Config, error) {
	kubeconfig := os.Getenv("KUBECONFIG")
	if kubeconfig == "" {
		home, err := os.UserHomeDir()
		if err != nil {
			return nil, fmt.Errorf("failed to get home dir: %w", err)
		}
		kubeconfig = filepath.Join(home, ".kube", "config")
	}

	if _, err := os.Stat(kubeconfig); os.IsNotExist(err) {
		return nil, fmt.Errorf("kubeconfig not found at %s", kubeconfig)
	}

	return clientcmd.BuildConfigFromFlags("", kubeconfig)
}

// ensureNamespace creates the test namespace if it doesn't exist.
func (s *TestServer) ensureNamespace(ctx context.Context) error {
	ns := &corev1.Namespace{
		ObjectMeta: metav1.ObjectMeta{
			Name: s.namespace,
		},
	}
	_, err := s.client.CoreV1().Namespaces().Create(ctx, ns, metav1.CreateOptions{})
	if err != nil && !isAlreadyExists(err) {
		return err
	}
	return nil
}

// isAlreadyExists checks if the error is an "already exists" error.
func isAlreadyExists(err error) bool {
	if err == nil {
		return false
	}
	errStr := err.Error()
	return contains(errStr, "already exists") || contains(errStr, "AlreadyExists")
}

func contains(s, substr string) bool {
	for i := 0; i <= len(s)-len(substr); i++ {
		if s[i:i+len(substr)] == substr {
			return true
		}
	}
	return false
}

// Namespace returns the test namespace.
func (s *TestServer) Namespace() string {
	return s.namespace
}

// Client returns the Kubernetes client.
func (s *TestServer) Client() kubernetes.Interface {
	return s.client
}

// CreatePod creates a Pod in the test server.
func (s *TestServer) CreatePod(ctx context.Context, pod *corev1.Pod) (*corev1.Pod, error) {
	pod = pod.DeepCopy()
	pod.Namespace = s.namespace
	return s.client.CoreV1().Pods(s.namespace).Create(ctx, pod, metav1.CreateOptions{})
}

// GetPod gets a Pod from the test server.
func (s *TestServer) GetPod(ctx context.Context, name string) (*corev1.Pod, error) {
	return s.client.CoreV1().Pods(s.namespace).Get(ctx, name, metav1.GetOptions{})
}

// UpdatePod updates a Pod in the test server.
func (s *TestServer) UpdatePod(ctx context.Context, pod *corev1.Pod) (*corev1.Pod, error) {
	pod = pod.DeepCopy()
	pod.Namespace = s.namespace
	return s.client.CoreV1().Pods(s.namespace).Update(ctx, pod, metav1.UpdateOptions{})
}

// UpdatePodStatus updates a Pod status in the test server.
func (s *TestServer) UpdatePodStatus(ctx context.Context, pod *corev1.Pod) (*corev1.Pod, error) {
	pod = pod.DeepCopy()
	pod.Namespace = s.namespace
	return s.client.CoreV1().Pods(s.namespace).UpdateStatus(ctx, pod, metav1.UpdateOptions{})
}

// CreateReplicaSet creates a ReplicaSet in the test server.
func (s *TestServer) CreateReplicaSet(ctx context.Context, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
	rs = rs.DeepCopy()
	rs.Namespace = s.namespace
	return s.client.AppsV1().ReplicaSets(s.namespace).Create(ctx, rs, metav1.CreateOptions{})
}

// GetReplicaSet gets a ReplicaSet from the test server.
func (s *TestServer) GetReplicaSet(ctx context.Context, name string) (*appsv1.ReplicaSet, error) {
	return s.client.AppsV1().ReplicaSets(s.namespace).Get(ctx, name, metav1.GetOptions{})
}

// UpdateReplicaSet updates a ReplicaSet in the test server.
func (s *TestServer) UpdateReplicaSet(ctx context.Context, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
	rs = rs.DeepCopy()
	rs.Namespace = s.namespace
	return s.client.AppsV1().ReplicaSets(s.namespace).Update(ctx, rs, metav1.UpdateOptions{})
}

// UpdateReplicaSetStatus updates a ReplicaSet status in the test server.
func (s *TestServer) UpdateReplicaSetStatus(ctx context.Context, rs *appsv1.ReplicaSet) (*appsv1.ReplicaSet, error) {
	rs = rs.DeepCopy()
	rs.Namespace = s.namespace
	return s.client.AppsV1().ReplicaSets(s.namespace).UpdateStatus(ctx, rs, metav1.UpdateOptions{})
}

// DeletePod deletes a Pod from the test server with optional DeleteOptions.
func (s *TestServer) DeletePod(ctx context.Context, name string, options metav1.DeleteOptions) error {
	return s.client.CoreV1().Pods(s.namespace).Delete(ctx, name, options)
}

// DeleteReplicaSet deletes a ReplicaSet from the test server with optional DeleteOptions.
func (s *TestServer) DeleteReplicaSet(ctx context.Context, name string, options metav1.DeleteOptions) error {
	return s.client.AppsV1().ReplicaSets(s.namespace).Delete(ctx, name, options)
}

// Cleanup cleans up all resources created by the test server.
func (s *TestServer) Cleanup(ctx context.Context) error {
	// Delete all pods in the namespace
	if err := s.client.CoreV1().Pods(s.namespace).DeleteCollection(
		ctx, metav1.DeleteOptions{}, metav1.ListOptions{}); err != nil {
		return err
	}
	// Delete all replicasets in the namespace
	if err := s.client.AppsV1().ReplicaSets(s.namespace).DeleteCollection(
		ctx, metav1.DeleteOptions{}, metav1.ListOptions{}); err != nil {
		return err
	}
	return nil
}

// Stop stops the test server.
// If using envtest, this stops the API server and etcd processes.
func (s *TestServer) Stop() error {
	if s.testEnv != nil {
		return s.testEnv.Stop()
	}
	return nil
}
