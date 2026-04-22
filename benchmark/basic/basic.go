package basic

func add(a int, b int) int {
	return a + b
}

func max(a int, b int) int {
	if a > b {
		return a
	}
	return b
}

func factorial(n int) int {
	if n < 0 {
		return 0
	}
	result := 1
	for i := 2; i <= n; i++ {
		result *= i
	}
	return result
}

func sum(values []int) int {
	total := 0
	for _, value := range values {
		total += value
	}
	return total
}

func reverseInts(values []int) []int {
	result := make([]int, len(values))
	for i, value := range values {
		result[len(values)-1-i] = value
	}
	return result
}

func filterPositive(values []int) []int {
	result := make([]int, 0, len(values))
	for _, value := range values {
		if value > 0 {
			result = append(result, value)
		}
	}
	return result
}

func frequencies(values []string) map[string]int {
	counts := make(map[string]int)
	for _, value := range values {
		counts[value]++
	}
	return counts
}

func binarySearch(sorted []int, target int) int {
	low := 0
	high := len(sorted) - 1
	for low <= high {
		mid := low + (high-low)/2
		if sorted[mid] == target {
			return mid
		}
		if sorted[mid] < target {
			low = mid + 1
		} else {
			high = mid - 1
		}
	}
	return -1
}

func mergeCounts(left map[string]int, right map[string]int) map[string]int {
	result := make(map[string]int, len(left)+len(right))
	for key, value := range left {
		result[key] = value
	}
	for key, value := range right {
		result[key] += value
	}
	return result
}

func uniqueStrings(values []string) []string {
	seen := make(map[string]bool)
	result := make([]string, 0, len(values))
	for _, value := range values {
		if !seen[value] {
			seen[value] = true
			result = append(result, value)
		}
	}
	return result
}

func selectionSort(values []int) []int {
	result := append([]int(nil), values...)
	for i := 0; i < len(result); i++ {
		minIndex := i
		for j := i + 1; j < len(result); j++ {
			if result[j] < result[minIndex] {
				minIndex = j
			}
		}
		result[i], result[minIndex] = result[minIndex], result[i]
	}
	return result
}

func insertionSort(values []int) []int {
	result := append([]int(nil), values...)
	for i := 1; i < len(result); i++ {
		value := result[i]
		j := i - 1
		for j >= 0 && result[j] > value {
			result[j+1] = result[j]
			j--
		}
		result[j+1] = value
	}
	return result
}

func quickSort(values []int) []int {
	result := append([]int(nil), values...)
	quickSortRange(result, 0, len(result)-1)
	return result
}

func quickSortRange(values []int, low int, high int) {
	if low >= high {
		return
	}
	pivot := partition(values, low, high)
	quickSortRange(values, low, pivot-1)
	quickSortRange(values, pivot+1, high)
}

func partition(values []int, low int, high int) int {
	pivot := values[high]
	store := low
	for i := low; i < high; i++ {
		if values[i] < pivot {
			values[i], values[store] = values[store], values[i]
			store++
		}
	}
	values[store], values[high] = values[high], values[store]
	return store
}
