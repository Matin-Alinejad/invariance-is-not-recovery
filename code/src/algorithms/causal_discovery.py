"""Constraint-based causal-discovery algorithms.

Provides the classical PC skeleton-search implementation and the
test-wise-deletion variant used by the experiments. The latter uses a separate
complete-case set for each conditional-independence query; it should not be read
as an implementation of additional missingness-graph corrections that are outside
the scope of this repository.
"""

import numpy as np
import pandas as pd
import networkx as nx
from typing import Dict, List, Tuple, Optional, Union
import logging
from itertools import combinations
from scipy.stats import pearsonr, spearmanr, rankdata, norm, t as student_t
from sklearn.linear_model import LinearRegression
from sklearn.preprocessing import StandardScaler

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class PCAlgorithm:
    """
    Implementation of the PC algorithm for causal discovery.
    This implementation provides the complete-data PC baseline used by the repository.
    """
    
    def __init__(self, alpha: float = 0.05, max_conditioning_set_size: int = 3,
                 ci_test: str = 'pearson'):
        """
        Initialize PC algorithm.
        
        Args:
            alpha: Significance level for independence tests
            max_conditioning_set_size: Maximum size of conditioning sets
        """
        self.alpha = alpha
        self.max_conditioning_set_size = max_conditioning_set_size
        self.ci_test = str(ci_test)
        if self.ci_test not in {'pearson', 'gaussian_copula'}:
            raise ValueError("ci_test must be 'pearson' or 'gaussian_copula'")
        self.graph = None
        self.separation_sets = {}
    
    @staticmethod
    def _sanitize_for_test(x: np.ndarray, y: np.ndarray,
                           z: Optional[np.ndarray] = None,
                           min_samples: int = 10,
                           max_abs: float = 1e12) -> Optional[Tuple[np.ndarray, np.ndarray, Optional[np.ndarray]]]:
        """
        Remove Inf/NaN and clip extreme values so downstream (LinearRegression, pearsonr) do not fail.
        Returns (x_clean, y_clean, z_clean) or None if too few valid rows.
        """
        x = np.asarray(x, dtype=np.float64).ravel()
        y = np.asarray(y, dtype=np.float64).ravel()
        n = len(x)
        if n != len(y):
            return None
        # Replace inf with nan, then drop rows where any of x, y or z is nan
        x_safe = np.where(np.isfinite(x), x, np.nan)
        y_safe = np.where(np.isfinite(y), y, np.nan)
        valid = np.isfinite(x_safe) & np.isfinite(y_safe)
        if z is not None:
            z = np.asarray(z, dtype=np.float64)
            if z.ndim == 1:
                z = z.reshape(-1, 1)
            z_safe = np.where(np.isfinite(z), z, np.nan)
            valid &= np.all(np.isfinite(z_safe), axis=1)
        else:
            z_safe = None
        valid = np.where(valid)[0]
        if len(valid) < min_samples:
            return None
        x_clean = np.clip(x_safe[valid], -max_abs, max_abs)
        y_clean = np.clip(y_safe[valid], -max_abs, max_abs)
        z_clean = np.clip(z_safe[valid], -max_abs, max_abs) if z_safe is not None else None
        return x_clean, y_clean, z_clean

    @staticmethod
    def _gaussian_copula_transform(values: np.ndarray) -> np.ndarray:
        """Column-wise rank-to-normal transform for continuous robustness checks."""
        arr = np.asarray(values, dtype=np.float64)
        one_dim = arr.ndim == 1
        if one_dim:
            arr = arr.reshape(-1, 1)
        out = np.empty_like(arr, dtype=np.float64)
        n = arr.shape[0]
        for j in range(arr.shape[1]):
            ranks = rankdata(arr[:, j], method='average')
            probs = (ranks - 0.5) / max(1, n)
            out[:, j] = norm.ppf(np.clip(probs, 1e-8, 1 - 1e-8))
        return out[:, 0] if one_dim else out

    def independence_test(self, x: np.ndarray, y: np.ndarray, 
                         z: Optional[np.ndarray] = None, *, min_samples: int = 10) -> Tuple[bool, float]:
        """
        Perform conditional independence test. Inputs are sanitized (Inf/NaN removed,
        extremes clipped) so all topologies (scale-free, small-world, random) run reliably.
        
        Args:
            x: First variable
            y: Second variable
            z: Conditioning set (optional)
            
        Returns:
            Tuple of (is_independent, p_value)
        """
        try:
            out = self._sanitize_for_test(x, y, z, min_samples=int(min_samples))
            if out is None:
                # A missing/ill-posed test is not evidence of independence.
                # Keeping the edge is the conservative skeleton decision.
                return False, 0.0
            x_clean, y_clean, z_clean = out
        except Exception:
            return False, 0.0

        if self.ci_test == 'gaussian_copula':
            x_clean = self._gaussian_copula_transform(x_clean)
            y_clean = self._gaussian_copula_transform(y_clean)
            if z_clean is not None:
                z_clean = self._gaussian_copula_transform(z_clean)

        if z_clean is None or (z_clean.ndim == 2 and z_clean.shape[1] == 0):
            # Unconditional independence test
            try:
                if len(np.unique(x_clean)) == 2 and len(np.unique(y_clean)) == 2:
                    from scipy.stats import chi2_contingency
                    contingency_table = pd.crosstab(x_clean, y_clean)
                    chi2, p_value, _, _ = chi2_contingency(contingency_table)
                    is_independent = p_value > self.alpha
                else:
                    corr, p_value = pearsonr(x_clean, y_clean)
                    is_independent = p_value > self.alpha
            except (ValueError, FloatingPointError, TypeError):
                is_independent, p_value = False, 0.0
        else:
            if z_clean.ndim == 1:
                z_clean = z_clean.reshape(-1, 1)
            try:
                reg_x = LinearRegression().fit(z_clean, x_clean)
                reg_y = LinearRegression().fit(z_clean, y_clean)
                x_residual = x_clean - reg_x.predict(z_clean)
                y_residual = y_clean - reg_y.predict(z_clean)
                corr = float(np.corrcoef(x_residual, y_residual)[0, 1])
                k = int(z_clean.shape[1])
                degrees_of_freedom = int(len(x_residual) - k - 2)
                if not np.isfinite(corr) or degrees_of_freedom <= 0:
                    return False, 0.0
                corr = float(np.clip(corr, -1 + 1e-15, 1 - 1e-15))
                statistic = abs(corr) * np.sqrt(degrees_of_freedom / max(1e-30, 1.0 - corr * corr))
                p_value = float(2.0 * student_t.sf(statistic, df=degrees_of_freedom))
                is_independent = p_value > self.alpha
            except (ValueError, FloatingPointError, TypeError, np.linalg.LinAlgError):
                # Do not replace a failed conditional test by an unconditional
                # test: that changes the null hypothesis.  Keep the edge.
                is_independent, p_value = False, 0.0

        return is_independent, p_value
    
    def find_adjacencies(self, data: pd.DataFrame) -> nx.Graph:
        """Find a PC-stable skeleton using conditioning sets from either endpoint."""
        variables = sorted(map(str, data.columns))
        graph = nx.Graph()
        graph.add_nodes_from(variables)
        graph.add_edges_from(combinations(variables, 2))
        self.separation_sets = {}

        level = 0
        while level <= self.max_conditioning_set_size:
            snapshot = {node: set(graph.neighbors(node)) for node in variables}
            any_testable = False
            for x, y in sorted(graph.edges()):
                if not graph.has_edge(x, y):
                    continue
                pools = (snapshot[x] - {y}, snapshot[y] - {x})
                if max(map(len, pools)) < level:
                    continue
                any_testable = True
                conditioning_sets = sorted({
                    tuple(c)
                    for pool in pools if len(pool) >= level
                    for c in combinations(tuple(sorted(pool)), level)
                })
                for cond in conditioning_sets:
                    z_data = data.loc[:, list(cond)].to_numpy() if cond else None
                    is_independent, _ = self.independence_test(
                        data[x].to_numpy(), data[y].to_numpy(), z_data
                    )
                    if is_independent:
                        graph.remove_edge(x, y)
                        self.separation_sets[(x, y)] = set(cond)
                        self.separation_sets[(y, x)] = set(cond)
                        break
            if not any_testable:
                break
            level += 1
        return graph

    def orient_edges(self, graph: nx.Graph, data: pd.DataFrame) -> nx.DiGraph:
        """
        Orient edges using conditional independence tests.
        
        Args:
            graph: Undirected graph
            data: Input data
            
        Returns:
            Directed graph
        """
        digraph = nx.DiGraph()
        digraph.add_nodes_from(graph.nodes())
        digraph.add_edges_from(graph.edges())
        
        variables = list(data.columns)
        
        # Apply orientation rules
        for size in range(self.max_conditioning_set_size + 1):
            edges_to_orient = []
            
            for edge in digraph.edges():
                x, y = edge
                
                # Find common neighbors
                x_neighbors = set(digraph.neighbors(x))
                y_neighbors = set(digraph.neighbors(y))
                common_neighbors = x_neighbors & y_neighbors
                
                # Try all conditioning sets of current size
                for conditioning_set in self._get_conditioning_sets(common_neighbors, size):
                    x_data = data[x].values
                    y_data = data[y].values
                    
                    if len(conditioning_set) > 0:
                        z_data = data[list(conditioning_set)].values
                    else:
                        z_data = None
                    
                    is_independent, _ = self.independence_test(x_data, y_data, z_data)
                    
                    if is_independent:
                        # Store separation set
                        self.separation_sets[(x, y)] = conditioning_set
                        self.separation_sets[(y, x)] = conditioning_set
                        edges_to_orient.append((x, y))
                        break
            
            # Remove oriented edges
            digraph.remove_edges_from(edges_to_orient)
        
        return digraph
    
    def _get_conditioning_sets(self, variables: set, size: int) -> List[set]:
        """
        Get all conditioning sets of given size.
        
        Args:
            variables: Set of variables
            size: Size of conditioning sets
            
        Returns:
            List of conditioning sets
        """
        from itertools import combinations
        
        if size == 0:
            return [set()]
        
        if size > len(variables):
            return []
        
        return [set(combo) for combo in combinations(variables, size)]
    
    def fit(self, data: pd.DataFrame) -> nx.DiGraph:
        """
        Run PC algorithm on data.
        
        Args:
            data: Input data
            
        Returns:
            Causal graph
        """
        logger.info("Running PC algorithm...")
        
        # Step 1: Find adjacencies (skeleton)
        undirected_graph = self.find_adjacencies(data)
        logger.info(f"Found {len(undirected_graph.edges())} adjacencies")

        # Step 2: Return skeleton as bidirected CPDAG (orientation not enforced here)
        directed_graph = nx.DiGraph()
        directed_graph.add_nodes_from(undirected_graph.nodes())
        for u, v in undirected_graph.edges():
            directed_graph.add_edge(u, v)
            directed_graph.add_edge(v, u)

        logger.info(f"Final graph has {len(directed_graph.edges())} edges")

        self.graph = directed_graph
        return directed_graph

class TestWiseDeletionPC:
    """PC skeleton search with a test-specific complete-case set for each CI query.

    The implementation is intentionally limited to the test-wise-deletion search
    studied in this repository. It does not add missingness-graph corrections that
    are not part of the registered computational design.
    """
    
    def __init__(self, alpha: float = 0.05, max_conditioning_set_size: int = 3,
                 missing_data_method: str = 'test_wise_deletion',
                 ci_test: str = 'pearson'):
        """
        Initialize the test-wise-deletion PC implementation.
        
        Args:
            alpha: Significance level for independence tests
            max_conditioning_set_size: Maximum size of conditioning sets
            missing_data_method: Method to handle missing data ('test_wise_deletion', 'imputation')
                                 'test_wise_deletion' uses the available cases for each CI query.
        """
        self.alpha = alpha
        self.max_conditioning_set_size = max_conditioning_set_size
        self.missing_data_method = missing_data_method
        self.ci_test = str(ci_test)
        self.graph = None
        self.separation_sets: Dict[Tuple[str, str], Tuple[str, ...]] = {}
        self.pc_algorithm = PCAlgorithm(alpha, max_conditioning_set_size, ci_test=self.ci_test)
    
    def handle_missing_data(self, data: pd.DataFrame) -> pd.DataFrame:
        """
        Handle missing data using specified method.
        
        Args:
            data: Data with missing values
            
        Returns:
            Data with missing values handled
        """
        if self.missing_data_method in ['complete_case', 'test_wise_deletion']:
            # Test-Wise Deletion: For the specific variables involved in the test (passed in 'data'),
            # remove rows with missing values. This maximizes sample size compared to list-wise deletion.
            return data.dropna()
        
        elif self.missing_data_method == 'imputation':
            # Simple imputation - fill missing values with median/mode
            processed_data = data.copy()
            
            for col in processed_data.columns:
                if processed_data[col].dtype == 'object':
                    # Categorical - use mode
                    mode_value = processed_data[col].mode()
                    if len(mode_value) > 0:
                        processed_data[col].fillna(mode_value[0], inplace=True)
                else:
                    # Numerical - use median
                    median_value = processed_data[col].median()
                    processed_data[col].fillna(median_value, inplace=True)
            
            return processed_data
        
        else:
            raise ValueError(f"Unknown missing data method: {self.missing_data_method}")
    
    def independence_test_with_missing(self, x: np.ndarray, y: np.ndarray,
                                     z: Optional[np.ndarray] = None) -> Tuple[bool, float]:
        """
        Perform independence test with missing data handling.
        
        Args:
            x: First variable
            y: Second variable
            z: Conditioning set (optional)
            
        Returns:
            Tuple of (is_independent, p_value)
        """
        # Create DataFrame for easier handling
        if z is None:
            df = pd.DataFrame({'x': x, 'y': y})
        else:
            if z.ndim == 1:
                z = z.reshape(-1, 1)
            df = pd.DataFrame({'x': x, 'y': y})
            for i in range(z.shape[1]):
                df[f'z_{i}'] = z[:, i]
        
        # Handle missing data
        df_clean = self.handle_missing_data(df)
        
        if len(df_clean) < 10:  # Too few observations: keep the edge
            return False, 0.0
        
        # Extract clean data
        x_clean = df_clean['x'].values
        y_clean = df_clean['y'].values
        
        if z is not None:
            z_cols = [col for col in df_clean.columns if col.startswith('z_')]
            if z_cols:
                z_clean = df_clean[z_cols].values
            else:
                z_clean = None
        else:
            z_clean = None
        
        # Perform independence test
        return self.pc_algorithm.independence_test(x_clean, y_clean, z_clean)
    
    def find_adjacencies_with_missing(self, data: pd.DataFrame) -> nx.Graph:
        """PC-stable skeleton search with a test-specific complete-case set."""
        variables = sorted(map(str, data.columns))
        graph = nx.Graph()
        graph.add_nodes_from(variables)
        graph.add_edges_from(combinations(variables, 2))
        self.separation_sets = {}

        level = 0
        while level <= self.max_conditioning_set_size:
            snapshot = {node: set(graph.neighbors(node)) for node in variables}
            any_testable = False
            for x, y in sorted(graph.edges()):
                if not graph.has_edge(x, y):
                    continue
                pools = (snapshot[x] - {y}, snapshot[y] - {x})
                if max(map(len, pools)) < level:
                    continue
                any_testable = True
                conditioning_sets = sorted({
                    tuple(c)
                    for pool in pools if len(pool) >= level
                    for c in combinations(tuple(sorted(pool)), level)
                })
                for cond in conditioning_sets:
                    z_data = data.loc[:, list(cond)].to_numpy() if cond else None
                    is_independent, _ = self.independence_test_with_missing(
                        data[x].to_numpy(), data[y].to_numpy(), z_data
                    )
                    if is_independent:
                        graph.remove_edge(x, y)
                        self.separation_sets[(x, y)] = tuple(cond)
                        self.separation_sets[(y, x)] = tuple(cond)
                        break
            if not any_testable:
                break
            level += 1
        return graph

    def find_local_adjacencies_with_missing(self, data: pd.DataFrame, target: str) -> set:
        """Order-stable target-only skeleton-neighborhood search."""
        variables = sorted(map(str, data.columns))
        if target not in variables:
            raise ValueError(f"Unknown target {target!r}")
        neighbors = {v for v in variables if v != target}
        for size in range(self.max_conditioning_set_size + 1):
            snapshot = set(neighbors)
            any_testable = False
            for x in sorted(snapshot):
                if x not in neighbors:
                    continue
                candidate_z = snapshot - {x}
                if len(candidate_z) < size:
                    continue
                any_testable = True
                for cond in combinations(tuple(sorted(candidate_z)), size):
                    z_data = data.loc[:, list(cond)].to_numpy() if cond else None
                    is_independent, _ = self.independence_test_with_missing(
                        data[target].to_numpy(), data[x].to_numpy(), z_data
                    )
                    if is_independent:
                        neighbors.discard(x)
                        self.separation_sets[(target, x)] = tuple(cond)
                        self.separation_sets[(x, target)] = tuple(cond)
                        break
            if not any_testable:
                break
        return neighbors

    def fit_local(self, data: pd.DataFrame, target: str) -> nx.DiGraph:
        """
        Run dedicated local test-wise-deletion PC around `target`.
        Returns a DiGraph with all nodes but only edges incident to target (bidirected).
        Use for local F1 evaluation only; global F1 is not meaningful.
        """
        data = data.copy()
        if np.any(np.isinf(data.values)) or np.any(np.abs(data.values) > 1e12):
            data = data.replace([np.inf, -np.inf], np.nan)
            data = data.clip(lower=-1e12, upper=1e12)
        adj_t = self.find_local_adjacencies_with_missing(data, target)
        digraph = nx.DiGraph()
        digraph.add_nodes_from(data.columns)
        for x in adj_t:
            digraph.add_edge(target, x)
            digraph.add_edge(x, target)
        return digraph
    
    def fit(self, data: pd.DataFrame) -> nx.DiGraph:
        """
        Run PC skeleton search using a test-specific complete-case set.
        
        Args:
            data: Input data with missing values
            
        Returns:
            Causal graph
        """
        logger.info("Running test-wise-deletion PC skeleton search...")
        logger.info(f"Missing data method: {self.missing_data_method}")
        # Sanitize: Inf/large values cause sklearn/scipy to fail (e.g. random topology at large p)
        data = data.copy()
        if np.any(np.isinf(data.values)) or np.any(np.abs(data.values) > 1e12):
            data = data.replace([np.inf, -np.inf], np.nan)
            data = data.clip(lower=-1e12, upper=1e12)
            logger.info("Input contained Inf/extreme values; replaced and clipped for numerical stability.")
        logger.info(f"Original data shape: {data.shape}")
        logger.info(f"Missing values: {data.isnull().sum().sum()}")
        
        # Step 1: Find adjacencies with missing data handling
        undirected_graph = self.find_adjacencies_with_missing(data)
        logger.info(f"Found {len(undirected_graph.edges())} adjacencies")

        # Step 2: Return skeleton as bidirected CPDAG (orientation not enforced here)
        digraph = nx.DiGraph()
        digraph.add_nodes_from(undirected_graph.nodes())
        for u, v in undirected_graph.edges():
            digraph.add_edge(u, v)
            digraph.add_edge(v, u)

        logger.info(f"Final graph has {len(digraph.edges())} edges")

        self.graph = digraph
        return digraph

class CausalGraphEvaluator:
    """
    Evaluator for comparing causal graphs.
    """
    
    def __init__(self):
        """Initialize the evaluator."""
        pass
    
    def structural_hamming_distance(self, true_graph: nx.DiGraph, 
                                  inferred_graph: nx.DiGraph) -> int:
        """
        Calculate Structural Hamming Distance (SHD) between graphs.
        
        Args:
            true_graph: True causal graph
            inferred_graph: Inferred causal graph
            
        Returns:
            SHD value
        """
        # Get all possible edges
        all_nodes = set(true_graph.nodes()) | set(inferred_graph.nodes())
        all_edges = set()
        
        for node1 in all_nodes:
            for node2 in all_nodes:
                if node1 != node2:
                    all_edges.add((node1, node2))
        
        # Count differences
        differences = 0
        
        for edge in all_edges:
            true_has_edge = true_graph.has_edge(*edge)
            inferred_has_edge = inferred_graph.has_edge(*edge)
            
            if true_has_edge != inferred_has_edge:
                differences += 1
        
        return differences
    
    def relative_structural_hamming_distance(self, true_graph: nx.DiGraph, 
                                           inferred_graph: nx.DiGraph) -> float:
        """
        Calculate Relative Structural Hamming Distance (relSHD) between graphs.
        
        relSHD is the SHD normalized by the maximum possible SHD for graphs
        of the same size, providing a value between 0 and 1 that indicates
        the proportion of differences relative to the maximum possible differences.
        
        Args:
            true_graph: True causal graph
            inferred_graph: Inferred causal graph
            
        Returns:
            relSHD value (0.0 to 1.0)
        """
        # Calculate SHD
        shd = self.structural_hamming_distance(true_graph, inferred_graph)
        
        # Get all nodes from both graphs
        all_nodes = set(true_graph.nodes()) | set(inferred_graph.nodes())
        n_nodes = len(all_nodes)
        
        # Maximum possible SHD is n*(n-1) for directed graphs
        # This represents the maximum number of possible directed edges
        max_possible_shd = n_nodes * (n_nodes - 1)
        
        # Handle edge case where there are no nodes
        if max_possible_shd == 0:
            return 0.0
        
        # Calculate relative SHD
        rel_shd = shd / max_possible_shd
        
        # Ensure the result is between 0 and 1
        return min(rel_shd, 1.0)
    
    def precision_recall(self, true_graph: nx.DiGraph, 
                        inferred_graph: nx.DiGraph) -> Tuple[float, float]:
        """
        Calculate precision and recall for edge detection.
        
        Args:
            true_graph: True causal graph
            inferred_graph: Inferred causal graph
            
        Returns:
            Tuple of (precision, recall)
        """
        true_edges = set(true_graph.edges())
        inferred_edges = set(inferred_graph.edges())
        
        if len(inferred_edges) == 0:
            precision = 0.0
        else:
            precision = len(true_edges & inferred_edges) / len(inferred_edges)
        
        if len(true_edges) == 0:
            recall = 0.0
        else:
            recall = len(true_edges & inferred_edges) / len(true_edges)
        
        return precision, recall
    
    def f1_score(self, true_graph: nx.DiGraph, 
                inferred_graph: nx.DiGraph) -> float:
        """
        Calculate F1 score for edge detection.
        
        Args:
            true_graph: True causal graph
            inferred_graph: Inferred causal graph
            
        Returns:
            F1 score
        """
        precision, recall = self.precision_recall(true_graph, inferred_graph)
        
        if precision + recall == 0:
            return 0.0
        
        return 2 * (precision * recall) / (precision + recall)
    
    def evaluate(self, true_graph: nx.DiGraph, 
                inferred_graph: nx.DiGraph) -> Dict[str, float]:
        """
        Comprehensive evaluation of inferred graph.
        
        Args:
            true_graph: True causal graph
            inferred_graph: Inferred causal graph
            
        Returns:
            Dictionary with evaluation metrics
        """
        precision, recall = self.precision_recall(true_graph, inferred_graph)
        f1 = self.f1_score(true_graph, inferred_graph)
        shd = self.structural_hamming_distance(true_graph, inferred_graph)
        rel_shd = self.relative_structural_hamming_distance(true_graph, inferred_graph)
        
        return {
            'precision': precision,
            'recall': recall,
            'f1_score': f1,
            'structural_hamming_distance': shd,
            'relative_structural_hamming_distance': rel_shd,
            'true_edges': len(true_graph.edges()),
            'inferred_edges': len(inferred_graph.edges()),
            'correct_edges': len(set(true_graph.edges()) & set(inferred_graph.edges()))
        }
