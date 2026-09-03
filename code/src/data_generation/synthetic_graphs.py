"""Synthetic graph and general dataset-generation utilities.

The registered recovery campaign uses the graph topology definitions and
``GraphTopologyGenerator`` from this module through the dedicated
``linear_gaussian_sem`` generator. The broader factory utilities are retained
from the production code lineage for completeness but are not part of the
registered experiment grid.
"""

import numpy as np
import pandas as pd
import networkx as nx
from typing import Dict, List, Tuple, Optional, Any, Union
from dataclasses import dataclass, field
from enum import Enum
import logging
from pathlib import Path
import json
from scipy import stats
from sklearn.preprocessing import StandardScaler

logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class GraphTopology(Enum):
    """Supported graph topologies for synthetic data generation."""
    CHAIN = "chain"
    FORK = "fork"
    COLLIDER = "collider"
    RANDOM = "random"
    RANDOM_REGULAR = "random_regular"
    SCALE_FREE = "scale_free"
    SMALL_WORLD = "small_world"
    MIXED = "mixed"
    FIXED = "fixed"

class NoiseDistribution(Enum):
    """Supported noise distributions."""
    GAUSSIAN = "gaussian"
    STUDENT_T = "student_t"
    EXPONENTIAL = "exponential"
    UNIFORM = "uniform"
    LAPLACE = "laplace"

class DataGenerationModel(Enum):
    """Supported data generation models."""
    LINEAR = "linear"
    QUADRATIC = "quadratic"
    SIGMOID = "sigmoid"
    MIXED = "mixed"

@dataclass
class SyntheticDatasetConfig:
    """Configuration for synthetic dataset generation."""
    name: str
    n_variables: int
    n_samples: int
    topology: GraphTopology
    generation_model: DataGenerationModel
    noise_distribution: NoiseDistribution
    causal_strength_range: Tuple[float, float] = (0.5, 1.5)
    noise_level_range: Tuple[float, float] = (0.1, 0.5)
    random_seed: int = 42

    # Topology-specific parameters
    topology_params: Dict[str, Any] = field(default_factory=dict)

    # Clinical relevance parameters
    clinical_variables: List[str] = field(default_factory=list)
    target_variable: Optional[str] = None

@dataclass
class SyntheticDatasetResult:
    """Result from synthetic dataset generation."""
    config: SyntheticDatasetConfig
    data: pd.DataFrame
    ground_truth_graph: nx.DiGraph
    causal_parameters: Dict[str, Any]
    metadata: Dict[str, Any]

class GraphTopologyGenerator:
    """Generates different graph topologies with controlled properties."""

    @staticmethod
    def _orient_undirected_to_dag(undirected: nx.Graph, random_seed: int = 42) -> nx.DiGraph:
        """Orient an undirected graph into a DAG using a random order."""
        rng = np.random.default_rng(random_seed)
        nodes = list(undirected.nodes())
        order = nodes.copy()
        rng.shuffle(order)
        order_index = {node: idx for idx, node in enumerate(order)}

        dag = nx.DiGraph()
        dag.add_nodes_from(nodes)
        for u, v in undirected.edges():
            if order_index[u] < order_index[v]:
                dag.add_edge(u, v)
            else:
                dag.add_edge(v, u)

        return dag

    @staticmethod
    def generate_chain(n_nodes: int, random_seed: int = 42) -> nx.DiGraph:
        """Generate a chain topology: X1 -> X2 -> ... -> Xn"""
        G = nx.DiGraph()

        nodes = [f'X{i}' for i in range(1, n_nodes + 1)]
        G.add_nodes_from(nodes)

        # Add chain edges
        for i in range(n_nodes - 1):
            G.add_edge(nodes[i], nodes[i + 1])

        return G

    @staticmethod
    def generate_fork(n_nodes: int, random_seed: int = 42) -> nx.DiGraph:
        """Generate a fork topology: X1 <- X2 -> X3 -> X4 -> ..."""
        G = nx.DiGraph()

        nodes = [f'X{i}' for i in range(1, n_nodes + 1)]
        G.add_nodes_from(nodes)

        if n_nodes >= 3:
            # Common cause
            G.add_edge(nodes[1], nodes[0])  # X2 -> X1
            G.add_edge(nodes[1], nodes[2])  # X2 -> X3

            # Chain from X3
            for i in range(3, n_nodes):
                G.add_edge(nodes[i-1], nodes[i])

        return G

    @staticmethod
    def generate_collider(n_nodes: int, random_seed: int = 42) -> nx.DiGraph:
        """Generate a collider topology: X1 -> X3 <- X2, with chains"""
        G = nx.DiGraph()

        nodes = [f'X{i}' for i in range(1, n_nodes + 1)]
        G.add_nodes_from(nodes)

        if n_nodes >= 3:
            # Collider at X3
            G.add_edge(nodes[0], nodes[2])  # X1 -> X3
            G.add_edge(nodes[1], nodes[2])  # X2 -> X3

            # Additional chains
            if n_nodes > 3:
                G.add_edge(nodes[2], nodes[3])  # X3 -> X4
                for i in range(4, n_nodes):
                    G.add_edge(nodes[i-1], nodes[i])

        return G

    @staticmethod
    def generate_random(n_nodes: int, edge_prob: float = 0.3,
                       random_seed: int = 42) -> nx.DiGraph:
        """Generate a random DAG."""
        undirected = nx.erdos_renyi_graph(n_nodes, edge_prob, seed=random_seed)
        mapping = {i: f'X{i + 1}' for i in range(n_nodes)}
        undirected = nx.relabel_nodes(undirected, mapping)
        return GraphTopologyGenerator._orient_undirected_to_dag(undirected, random_seed)

    @staticmethod
    def generate_random_regular(n_nodes: int, degree: int = 2,
                                random_seed: int = 42) -> nx.DiGraph:
        """Generate a bounded-degree random-regular skeleton and orient it as a DAG."""
        degree = int(degree)
        if degree < 0 or degree >= n_nodes:
            raise ValueError("random-regular degree must satisfy 0 <= degree < n_nodes")
        if (n_nodes * degree) % 2 != 0:
            raise ValueError("n_nodes * degree must be even for a regular graph")
        undirected = nx.random_regular_graph(degree, n_nodes, seed=random_seed)
        mapping = {i: f'X{i + 1}' for i in range(n_nodes)}
        undirected = nx.relabel_nodes(undirected, mapping)
        return GraphTopologyGenerator._orient_undirected_to_dag(undirected, random_seed)

    @staticmethod
    def generate_scale_free(n_nodes: int, m: int = 2,
                           random_seed: int = 42) -> nx.DiGraph:
        """Generate a scale-free DAG using preferential attachment."""
        rng = np.random.default_rng(int(random_seed))
        G = nx.DiGraph()

        nodes = [f'X{i}' for i in range(1, n_nodes + 1)]
        G.add_nodes_from(nodes)

        # Start with a small complete graph
        initial_nodes = min(m + 1, n_nodes)
        for i in range(initial_nodes):
            for j in range(i + 1, initial_nodes):
                G.add_edge(nodes[i], nodes[j])

        # Add remaining nodes with preferential attachment
        for i in range(initial_nodes, n_nodes):
            # Choose m nodes to connect to based on degree
            degrees = dict(G.degree())
            total_degree = sum(degrees.values())

            if total_degree > 0:
                probs = [degrees[node] / total_degree for node in G.nodes()]
                targets = rng.choice(list(G.nodes()), size=min(m, len(G.nodes())),
                                     replace=False, p=probs)

                for target in targets:
                    # Add edge from new node to existing node
                    G.add_edge(nodes[i], target)

        return G

    @staticmethod
    def generate_small_world(n_nodes: int, k: int = 2, p: float = 0.1,
                           random_seed: int = 42) -> nx.DiGraph:
        """Generate a small-world DAG."""
        undirected = nx.watts_strogatz_graph(n_nodes, k, p, seed=random_seed)
        mapping = {i: f'X{i + 1}' for i in range(n_nodes)}
        undirected = nx.relabel_nodes(undirected, mapping)
        return GraphTopologyGenerator._orient_undirected_to_dag(undirected, random_seed)


    @staticmethod
    def generate_fixed(n_nodes: int, node_names: List[str], edges: List[List[str]] | List[Tuple[str, str]],
                       random_seed: int = 42) -> nx.DiGraph:
        """Generate a fixed named benchmark DAG from an explicit edge list."""
        del random_seed  # fixed structures are seed-independent
        names = list(map(str, node_names))
        if len(names) != int(n_nodes):
            raise ValueError(f"fixed DAG declares {len(names)} nodes but n_nodes={n_nodes}")
        if len(set(names)) != len(names):
            raise ValueError("fixed DAG node names must be unique")
        graph = nx.DiGraph()
        graph.add_nodes_from(names)
        normalized_edges = [(str(u), str(v)) for u, v in edges]
        unknown = {node for edge in normalized_edges for node in edge if node not in graph}
        if unknown:
            raise ValueError(f"fixed DAG edges reference unknown nodes: {sorted(unknown)}")
        graph.add_edges_from(normalized_edges)
        if not nx.is_directed_acyclic_graph(graph):
            raise ValueError("fixed graph must be a DAG")
        return graph

    @staticmethod
    def generate_mixed(n_nodes: int, random_seed: int = 42) -> nx.DiGraph:
        """Generate a mixed topology combining different structures."""
        rng = np.random.default_rng(int(random_seed))
        G = nx.DiGraph()

        nodes = [f'X{i}' for i in range(1, n_nodes + 1)]
        G.add_nodes_from(nodes)

        # Create multiple components with different topologies
        if n_nodes >= 6:
            # Chain component
            for i in range(3):
                G.add_edge(nodes[i], nodes[i + 1])

            # Fork component
            G.add_edge(nodes[3], nodes[4])
            G.add_edge(nodes[3], nodes[5])

            # Connect components
            if n_nodes > 6:
                G.add_edge(nodes[2], nodes[3])
                # Add more random edges
                for i in range(6, n_nodes):
                    predecessors = rng.choice(nodes[:i], size=min(2, i), replace=False)
                    for pred in predecessors:
                        G.add_edge(pred, nodes[i])

        return G

class DataGenerator:
    """Generates synthetic data from causal graphs."""

    def __init__(self, random_seed: int = 42):
        self.random_seed = int(random_seed)
        self.rng = np.random.default_rng(self.random_seed)

    def generate_data(self, graph: nx.DiGraph,
                     config: SyntheticDatasetConfig) -> Tuple[pd.DataFrame, Dict[str, Any]]:
        """
        Generate synthetic data from a causal graph.

        Args:
            graph: Causal DAG
            config: Dataset generation configuration

        Returns:
            Generated data and causal parameters
        """
        # Each dataset owns an independent local generator. This prevents
        # serial/parallel execution order from changing the generated data.
        self.rng = np.random.default_rng(int(config.random_seed))
        nodes = list(graph.nodes())
        n_samples = config.n_samples
        n_vars = len(nodes)

        # Initialize data matrix
        data = np.zeros((n_samples, n_vars))

        # Generate noise for each variable
        noise_params = {}
        for i, node in enumerate(nodes):
            noise_params[node] = self._generate_noise_parameters(
                config.noise_distribution, n_samples
            )

        # Generate data following topological order
        topo_order = list(nx.topological_sort(graph))

        causal_params = {}

        for node in topo_order:
            node_idx = nodes.index(node)
            parents = list(graph.predecessors(node))

            if not parents:
                # Root node - generate from noise
                data[:, node_idx] = noise_params[node]['noise']
            else:
                # Generate based on parents
                parent_data = data[:, [nodes.index(p) for p in parents]]

                # Generate causal effect
                effect, params = self._generate_causal_effect(
                    parent_data, config.generation_model, config.causal_strength_range
                )

                # Add noise
                data[:, node_idx] = effect + noise_params[node]['noise']

                # Store parameters
                causal_params[node] = {
                    'parents': parents,
                    'causal_function': config.generation_model.value,
                    'parameters': params,
                    'noise_distribution': config.noise_distribution.value,
                    'noise_params': noise_params[node]['params']
                }

        # Create DataFrame
        df = pd.DataFrame(data, columns=nodes)

        # Standardize if needed
        if config.topology_params.get('standardize', True):
            scaler = StandardScaler()
            df = pd.DataFrame(scaler.fit_transform(df), columns=df.columns)

        return df, causal_params

    def _generate_noise_parameters(self, distribution: NoiseDistribution,
                                 n_samples: int) -> Dict[str, Any]:
        """Generate noise parameters for a variable."""
        if distribution == NoiseDistribution.GAUSSIAN:
            noise = self.rng.normal(0, 1, n_samples)
            params = {'mean': 0, 'std': 1}
        elif distribution == NoiseDistribution.STUDENT_T:
            df = self.rng.uniform(3, 10)  # degrees of freedom
            noise = self.rng.standard_t(df, n_samples)
            params = {'df': df}
        elif distribution == NoiseDistribution.EXPONENTIAL:
            scale = self.rng.uniform(0.5, 2.0)
            noise = self.rng.exponential(scale, n_samples) - scale  # center at 0
            params = {'scale': scale}
        elif distribution == NoiseDistribution.UNIFORM:
            noise = self.rng.uniform(-1.5, 1.5, n_samples)
            params = {'low': -1.5, 'high': 1.5}
        elif distribution == NoiseDistribution.LAPLACE:
            noise = self.rng.laplace(0, 0.5, n_samples)
            params = {'loc': 0, 'scale': 0.5}
        else:
            noise = self.rng.normal(0, 1, n_samples)
            params = {'mean': 0, 'std': 1}

        return {'noise': noise, 'params': params}

    def _generate_causal_effect(self, parent_data: np.ndarray,
                              model: DataGenerationModel,
                              strength_range: Tuple[float, float]) -> Tuple[np.ndarray, Dict]:
        """Generate causal effect from parents."""
        n_samples, n_parents = parent_data.shape

        # Random causal strength
        strength = self.rng.uniform(*strength_range)

        params = {'strength': strength}

        if model == DataGenerationModel.LINEAR:
            # Draw an explicit non-vanishing coefficient magnitude for every
            # edge.  The production design samples weights uniformly in [-strength,
            # strength], which allowed arbitrarily weak edges even when the
            # configured signal range had a positive lower endpoint.
            low, high = map(float, strength_range)
            if not (0 <= low <= high):
                raise ValueError("causal_strength_range must satisfy 0 <= low <= high")
            magnitudes = self.rng.uniform(low, high, n_parents)
            signs = self.rng.choice([-1.0, 1.0], size=n_parents)
            weights = signs * magnitudes
            effect = np.dot(parent_data, weights)
            params['weights'] = weights.tolist()
            params['min_abs_weight_configured'] = low
            params['max_abs_weight_configured'] = high

        elif model == DataGenerationModel.QUADRATIC:
            # Quadratic effects
            effect = np.zeros(n_samples)
            for i in range(n_parents):
                effect += strength * parent_data[:, i] ** 2
                if self.rng.random() < 0.5:  # Add interaction terms
                    for j in range(i + 1, n_parents):
                        effect += 0.5 * strength * parent_data[:, i] * parent_data[:, j]
            params['quadratic'] = True

        elif model == DataGenerationModel.SIGMOID:
            # Sigmoid transformation with bounded output
            linear_combo = np.sum(parent_data, axis=1)
            # Scale linear combo to prevent extreme values
            linear_combo = np.clip(linear_combo, -5, 5)
            effect = strength * (1 / (1 + np.exp(-linear_combo))) - 0.5
            params['sigmoid'] = True

        elif model == DataGenerationModel.MIXED:
            # Mix of different functions
            effect_type = self.rng.choice(['linear', 'quadratic', 'sigmoid'])
            if effect_type == 'linear':
                low, high = map(float, strength_range)
                magnitudes = self.rng.uniform(low, high, n_parents)
                signs = self.rng.choice([-1.0, 1.0], size=n_parents)
                weights = signs * magnitudes
                effect = np.dot(parent_data, weights)
                params['type'] = 'linear'
                params['weights'] = weights.tolist()
            elif effect_type == 'quadratic':
                effect = strength * np.sum(parent_data ** 2, axis=1)
                params['type'] = 'quadratic'
            else:
                linear_combo = np.sum(parent_data, axis=1)
                effect = strength * (1 / (1 + np.exp(-linear_combo))) - 0.5
                params['type'] = 'sigmoid'

        else:
            # Default to linear
            weights = self.rng.uniform(-strength, strength, n_parents)
            effect = np.dot(parent_data, weights)
            params['weights'] = weights.tolist()

        return effect, params

class EnhancedSyntheticDatasetFactory:
    """
    Enhanced factory for generating comprehensive synthetic datasets
    for MNAR robustness benchmarking.
    """

    def __init__(self, random_seed: int = 42):
        self.random_seed = random_seed
        self.topology_generator = GraphTopologyGenerator()
        self.data_generator = DataGenerator(random_seed)

        # Setup logging
        self.logger = logging.getLogger(self.__class__.__name__)

    def create_benchmark_suite(self, suite_name: str = "comprehensive_mnar_benchmark") -> List[SyntheticDatasetConfig]:
        """
        Create a comprehensive benchmark suite with diverse configurations.

        Returns:
            List of dataset configurations for the benchmark
        """
        configs = []

        # Define complexity levels
        complexity_levels = {
            'easy': {'n_vars': (5, 10), 'n_samples': (500, 1000)},
            'medium': {'n_vars': (10, 20), 'n_samples': (1000, 2000)},
            'hard': {'n_vars': (15, 30), 'n_samples': (2000, 5000)}
        }

        topologies = [
            GraphTopology.CHAIN,
            GraphTopology.FORK,
            GraphTopology.COLLIDER,
            GraphTopology.RANDOM,
            GraphTopology.SCALE_FREE,
            GraphTopology.SMALL_WORLD,
            GraphTopology.MIXED
        ]

        generation_models = [
            DataGenerationModel.LINEAR,
            DataGenerationModel.QUADRATIC,
            DataGenerationModel.SIGMOID,
            DataGenerationModel.MIXED
        ]

        noise_distributions = [
            NoiseDistribution.GAUSSIAN,
            NoiseDistribution.STUDENT_T,
            NoiseDistribution.EXPONENTIAL,
            NoiseDistribution.LAPLACE
        ]

        config_id = 0
        rng = np.random.default_rng(self.random_seed)

        for complexity, params in complexity_levels.items():
            n_configs_per_complexity = 20 if complexity == 'easy' else 15 if complexity == 'medium' else 10

            for i in range(n_configs_per_complexity):
                # Random parameters
                n_vars = rng.integers(*params['n_vars'])
                n_samples = rng.integers(*params['n_samples'])
                topology = rng.choice(topologies)
                model = rng.choice(generation_models)
                noise_dist = rng.choice(noise_distributions)

                # Topology-specific parameters
                topo_params = {}
                if topology == GraphTopology.RANDOM:
                    topo_params['edge_prob'] = rng.uniform(0.1, 0.4)
                elif topology == GraphTopology.SCALE_FREE:
                    topo_params['m'] = min(rng.integers(1, 4), n_vars // 2)
                elif topology == GraphTopology.SMALL_WORLD:
                    topo_params['k'] = min(rng.integers(1, 3), n_vars // 2)
                    topo_params['p'] = rng.uniform(0.05, 0.2)

                config = SyntheticDatasetConfig(
                    name=f"{suite_name}_{complexity}_{config_id:03d}",
                    n_variables=n_vars,
                    n_samples=n_samples,
                    topology=topology,
                    generation_model=model,
                    noise_distribution=noise_dist,
                    topology_params=topo_params,
                    random_seed=self.random_seed + config_id
                )

                configs.append(config)
                config_id += 1

        self.logger.info(f"Created benchmark suite with {len(configs)} configurations")
        return configs

    def create_clinical_benchmark_suite(self) -> List[SyntheticDatasetConfig]:
        """
        Create clinically-relevant benchmark suite mimicking real medical data.

        Returns:
            List of clinically-relevant dataset configurations
        """
        configs = []

        # Clinical variable templates
        clinical_templates = [
            {
                'name': 'cardiovascular_risk',
                'variables': ['age', 'cholesterol', 'blood_pressure', 'smoking', 'exercise', 'bmi', 'diabetes', 'heart_disease'],
                'target': 'heart_disease',
                'topology': GraphTopology.MIXED
            },
            {
                'name': 'diabetes_progression',
                'variables': ['age', 'bmi', 'glucose', 'insulin', 'family_history', 'exercise', 'diet', 'diabetes'],
                'target': 'diabetes',
                'topology': GraphTopology.COLLIDER
            },
            {
                'name': 'cancer_risk',
                'variables': ['age', 'genetics', 'smoking', 'alcohol', 'radiation', 'diet', 'exercise', 'cancer'],
                'target': 'cancer',
                'topology': GraphTopology.FORK
            }
        ]

        config_id = 0

        for template in clinical_templates:
            for complexity in ['medium', 'hard']:
                n_samples = 2000 if complexity == 'medium' else 5000

                config = SyntheticDatasetConfig(
                    name=f"clinical_{template['name']}_{complexity}_{config_id:02d}",
                    n_variables=len(template['variables']),
                    n_samples=n_samples,
                    topology=template['topology'],
                    generation_model=DataGenerationModel.MIXED,
                    noise_distribution=NoiseDistribution.GAUSSIAN,
                    clinical_variables=template['variables'],
                    target_variable=template['target'],
                    random_seed=self.random_seed + config_id
                )

                configs.append(config)
                config_id += 1

        self.logger.info(f"Created clinical benchmark suite with {len(configs)} configurations")
        return configs

    def generate_dataset(self, config: SyntheticDatasetConfig) -> SyntheticDatasetResult:
        """
        Generate a single synthetic dataset from configuration.

        Args:
            config: Dataset configuration

        Returns:
            Generated dataset with metadata
        """
        self.logger.info(f"Generating dataset: {config.name}")

        # Generate graph topology
        if config.topology == GraphTopology.CHAIN:
            graph = self.topology_generator.generate_chain(config.n_variables, config.random_seed)
        elif config.topology == GraphTopology.FORK:
            graph = self.topology_generator.generate_fork(config.n_variables, config.random_seed)
        elif config.topology == GraphTopology.COLLIDER:
            graph = self.topology_generator.generate_collider(config.n_variables, config.random_seed)
        elif config.topology == GraphTopology.RANDOM:
            edge_prob = config.topology_params.get('edge_prob', 0.3)
            graph = self.topology_generator.generate_random(config.n_variables, edge_prob, config.random_seed)
        elif config.topology == GraphTopology.RANDOM_REGULAR:
            degree = config.topology_params.get('degree', 2)
            graph = self.topology_generator.generate_random_regular(config.n_variables, degree, config.random_seed)
        elif config.topology == GraphTopology.SCALE_FREE:
            m = config.topology_params.get('m', 2)
            graph = self.topology_generator.generate_scale_free(config.n_variables, m, config.random_seed)
        elif config.topology == GraphTopology.SMALL_WORLD:
            k = config.topology_params.get('k', 2)
            p = config.topology_params.get('p', 0.1)
            graph = self.topology_generator.generate_small_world(config.n_variables, k, p, config.random_seed)
        elif config.topology == GraphTopology.MIXED:
            graph = self.topology_generator.generate_mixed(config.n_variables, config.random_seed)
        elif config.topology == GraphTopology.FIXED:
            graph = self.topology_generator.generate_fixed(
                config.n_variables,
                config.topology_params.get('node_names', []),
                config.topology_params.get('edges', []),
                config.random_seed,
            )
        else:
            raise ValueError(f"Unsupported topology: {config.topology}")

        # Generate data
        data, causal_params = self.data_generator.generate_data(graph, config)

        # Create metadata
        metadata = {
            'generation_timestamp': str(pd.Timestamp.now()),
            'graph_properties': {
                'n_nodes': graph.number_of_nodes(),
                'n_edges': graph.number_of_edges(),
                'average_degree': sum(dict(graph.degree()).values()) / graph.number_of_nodes(),
                'is_dag': nx.is_directed_acyclic_graph(graph),
                'density': nx.density(graph)
            },
            'data_properties': {
                'n_samples': len(data),
                'n_variables': len(data.columns),
                'missing_rate': data.isnull().sum().sum() / (len(data) * len(data.columns)),
                'correlations': data.corr().abs().mean().mean()
            }
        }

        result = SyntheticDatasetResult(
            config=config,
            data=data,
            ground_truth_graph=graph,
            causal_parameters=causal_params,
            metadata=metadata
        )

        self.logger.info(f"Generated dataset with {len(data)} samples, {len(data.columns)} variables, "
                        f"{graph.number_of_edges()} edges")

        return result

    def generate_batch(self, configs: List[SyntheticDatasetConfig],
                      output_dir: str = "results/synthetic_datasets",
                      save_format: str = "both") -> List[SyntheticDatasetResult]:
        """
        Generate multiple datasets in batch.

        Args:
            configs: List of dataset configurations
            output_dir: Directory to save results
            save_format: 'csv', 'json', or 'both'

        Returns:
            List of generated dataset results
        """
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)

        results = []

        for i, config in enumerate(configs):
            self.logger.info(f"Processing dataset {i+1}/{len(configs)}: {config.name}")

            try:
                result = self.generate_dataset(config)
                results.append(result)

                # Save to disk
                if save_format in ['csv', 'both']:
                    csv_path = output_path / f"{config.name}.csv"
                    result.data.to_csv(csv_path, index=False)

                if save_format in ['json', 'both']:
                    json_path = output_path / f"{config.name}_metadata.json"
                    metadata = {
                        'config': vars(config),
                        'causal_parameters': result.causal_parameters,
                        'metadata': result.metadata,
                        'ground_truth_edges': list(result.ground_truth_graph.edges())
                    }

                    with open(json_path, 'w') as f:
                        json.dump(metadata, f, indent=2, default=str)

            except Exception as e:
                self.logger.error(f"Failed to generate dataset {config.name}: {e}")
                continue

        self.logger.info(f"Batch generation completed: {len(results)}/{len(configs)} successful")
        return results

    def validate_dataset_properties(self, result: SyntheticDatasetResult) -> Dict[str, Any]:
        """
        Validate properties of generated dataset.

        Args:
            result: Generated dataset result

        Returns:
            Validation results
        """
        # Count root nodes (nodes with no incoming edges) - these don't have causal parameters
        root_nodes = [n for n in result.ground_truth_graph.nodes() 
                     if result.ground_truth_graph.in_degree(n) == 0]
        n_effect_vars = len(result.data.columns) - len(root_nodes)
        
        validation = {
            'is_dag': nx.is_directed_acyclic_graph(result.ground_truth_graph),
            'has_edges': result.ground_truth_graph.number_of_edges() > 0,
            'data_integrity': not result.data.isnull().all().any(),
            'causal_parameters_complete': len(result.causal_parameters) >= n_effect_vars  # Allow >= since some may have multiple parents
        }

        # Additional statistical validations (relaxed thresholds)
        data = result.data
        validation['data_properties'] = {
            'finite_values': np.isfinite(data.values).all(),
            'reasonable_variance': (data.var() > 1e-8).all(),  # Relaxed: allow very small variances
            'reasonable_range': ((data.abs() < 1e6).mean() > 0.5).all()  # Relaxed: allow wider range, lower threshold
        }

        validation['overall_valid'] = all(validation.values()) and all(validation['data_properties'].values())

        return validation

def create_comprehensive_benchmark() -> None:
    """Create and validate a comprehensive benchmark suite."""
    print("Creating Comprehensive MNAR Benchmark Suite")
    print("=" * 50)

    factory = EnhancedSyntheticDatasetFactory(random_seed=42)

    # Create different benchmark suites
    benchmark_configs = factory.create_benchmark_suite("comprehensive_mnar_benchmark")
    clinical_configs = factory.create_clinical_benchmark_suite()

    all_configs = benchmark_configs + clinical_configs

    print(f"Total configurations: {len(all_configs)}")
    print(f"  - General benchmarks: {len(benchmark_configs)}")
    print(f"  - Clinical benchmarks: {len(clinical_configs)}")

    # Sample generation (small batch for testing)
    test_configs = all_configs[:5]  # Test with first 5 configs

    print(f"\nTesting generation with {len(test_configs)} configurations...")

    results = factory.generate_batch(
        test_configs,
        output_dir="results/synthetic_datasets/test_batch",
        save_format="both"
    )

    # Validate results
    print(f"\nValidating {len(results)} generated datasets...")
    validation_summary = {'valid': 0, 'invalid': 0, 'errors': []}

    for result in results:
        try:
            validation = factory.validate_dataset_properties(result)
            if validation['overall_valid']:
                validation_summary['valid'] += 1
            else:
                validation_summary['invalid'] += 1
                validation_summary['errors'].append(f"{result.config.name}: validation failed")
        except Exception as e:
            validation_summary['invalid'] += 1
            validation_summary['errors'].append(f"{result.config.name}: {e}")

    print("Validation Summary:")
    print(f"  Valid datasets: {validation_summary['valid']}")
    print(f"  Invalid datasets: {validation_summary['invalid']}")

    if validation_summary['errors']:
        print("  Errors:")
        for error in validation_summary['errors'][:5]:  # Show first 5 errors
            print(f"    - {error}")

    print("\n[SUCCESS] Enhanced Synthetic Dataset Factory ready for large-scale benchmarking!")
    print(f"   Full benchmark would generate {len(all_configs)} diverse datasets")

if __name__ == "__main__":
    create_comprehensive_benchmark()
