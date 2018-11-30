import SyncCircuitGraph
import CircuitGraph

def main():
    netlist = None
    with open('./ncl_umult/umult10.txt', 'rb') as r_file:
        netlist = r_file.read()

    # cir_graph = SyncCircuitGraph.SyncCircuitGraph(netlist)
    cir_graph = CircuitGraph.CircuitGraph(netlist)
    graph = cir_graph.get_graph()

    # print graph
    print cir_graph.get_graph_levels()

if __name__ == '__main__':
    main()