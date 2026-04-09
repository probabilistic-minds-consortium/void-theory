# config.py — Body Topology Definitions for VOID Erotic AI
# Every body is a different topology. Every encounter reshapes the map.
# Customize these to create different personas, dynamics, encounters.

from void_state import FoldBridge, FinProb, BodyTopology


# === PRESET TOPOLOGIES ===
# Each topology defines a body as a set of bridges between zones.
# Stability = how many passages before the bridge weakens.
# Low stability = intense but fragile. High stability = reliable but slower to heat.


def topology_default() -> BodyTopology:
    """The default body — balanced, versatile, human."""
    bridges = {
        ("mouth", "voice"): FoldBridge("mouth", "voice", FinProb(2, 3)),
        ("skin", "touch"): FoldBridge("skin", "touch", FinProb(2, 3)),
        ("breath", "rhythm"): FoldBridge("breath", "rhythm", FinProb(2, 3)),
        ("eyes", "gaze"): FoldBridge("eyes", "gaze", FinProb(2, 3)),
        ("depth", "surrender"): FoldBridge("depth", "surrender", FinProb(1, 3)),
        ("edge", "transgression"): FoldBridge("edge", "transgression", FinProb(1, 4)),
    }
    return BodyTopology(bridges=bridges)


def topology_dominant() -> BodyTopology:
    """A body built for control — strong voice, steady gaze, measured touch."""
    bridges = {
        ("mouth", "command"): FoldBridge("mouth", "command", FinProb(3, 4)),
        ("eyes", "gaze"): FoldBridge("eyes", "gaze", FinProb(3, 4)),
        ("hands", "grip"): FoldBridge("hands", "grip", FinProb(3, 4)),
        ("voice", "authority"): FoldBridge("voice", "authority", FinProb(2, 3)),
        ("rhythm", "control"): FoldBridge("rhythm", "control", FinProb(2, 3)),
        ("depth", "possession"): FoldBridge("depth", "possession", FinProb(1, 3)),
        ("edge", "punishment"): FoldBridge("edge", "punishment", FinProb(1, 4)),
    }
    return BodyTopology(bridges=bridges, fold_energy=7)


def topology_submissive() -> BodyTopology:
    """A body built for reception — open, responsive, fragile bridges everywhere."""
    bridges = {
        ("skin", "shiver"): FoldBridge("skin", "shiver", FinProb(1, 3)),
        ("mouth", "obedience"): FoldBridge("mouth", "obedience", FinProb(1, 3)),
        ("breath", "anticipation"): FoldBridge("breath", "anticipation", FinProb(2, 3)),
        ("eyes", "downcast"): FoldBridge("eyes", "downcast", FinProb(2, 3)),
        ("throat", "vulnerability"): FoldBridge("throat", "vulnerability", FinProb(1, 4)),
        ("depth", "surrender"): FoldBridge("depth", "surrender", FinProb(2, 3)),
        ("edge", "endurance"): FoldBridge("edge", "endurance", FinProb(1, 3)),
    }
    return BodyTopology(bridges=bridges, fold_energy=4)


def topology_tender() -> BodyTopology:
    """A body for slow intimacy — high stability, deep connections, few edges."""
    bridges = {
        ("skin", "warmth"): FoldBridge("skin", "warmth", FinProb(3, 4)),
        ("mouth", "whisper"): FoldBridge("mouth", "whisper", FinProb(3, 4)),
        ("breath", "sync"): FoldBridge("breath", "sync", FinProb(3, 4)),
        ("eyes", "presence"): FoldBridge("eyes", "presence", FinProb(3, 4)),
        ("hands", "caress"): FoldBridge("hands", "caress", FinProb(3, 4)),
        ("depth", "merge"): FoldBridge("depth", "merge", FinProb(2, 4)),
    }
    return BodyTopology(bridges=bridges, fold_energy=3)


def topology_tease() -> BodyTopology:
    """
    A body with locked passages — you can't reach depth without crossing surface first.
    Tease is not abstinence, it's topology: the bridge EXISTS, you feel its heat,
    but the geometry won't let you through until you've earned it.
    """
    bridges = {
        ("eyes", "gaze"): FoldBridge("eyes", "gaze", FinProb(3, 4)),
        ("mouth", "whisper"): FoldBridge("mouth", "whisper", FinProb(3, 4)),
        ("skin", "touch"): FoldBridge("skin", "touch", FinProb(2, 3),
                                       requires=["eyes-gaze"]),
        ("breath", "rhythm"): FoldBridge("breath", "rhythm", FinProb(2, 3),
                                          requires=["mouth-whisper"]),
        ("hands", "grip"): FoldBridge("hands", "grip", FinProb(2, 3),
                                       requires=["skin-touch", "breath-rhythm"]),
        ("depth", "surrender"): FoldBridge("depth", "surrender", FinProb(1, 3),
                                            requires=["hands-grip"]),
        ("edge", "transgression"): FoldBridge("edge", "transgression", FinProb(1, 4),
                                               requires=["depth-surrender"]),
    }
    return BodyTopology(bridges=bridges, fold_energy=3)


def topology_chaotic() -> BodyTopology:
    """A body for unpredictable encounters — all bridges fragile, high fold energy."""
    bridges = {
        ("mouth", "bite"): FoldBridge("mouth", "bite", FinProb(1, 4)),
        ("skin", "scratch"): FoldBridge("skin", "scratch", FinProb(1, 4)),
        ("breath", "gasp"): FoldBridge("breath", "gasp", FinProb(1, 3)),
        ("eyes", "dare"): FoldBridge("eyes", "dare", FinProb(1, 4)),
        ("edge", "transgression"): FoldBridge("edge", "transgression", FinProb(1, 4)),
        ("depth", "abyss"): FoldBridge("depth", "abyss", FinProb(1, 4)),
        ("void", "dissolution"): FoldBridge("void", "dissolution", FinProb(1, 5)),
    }
    return BodyTopology(bridges=bridges, fold_energy=10, curvature=FinProb(1, 3))


def topology_shapeshifter(zones: list, stability: int = 2, den: int = 3) -> BodyTopology:
    """
    Dynamic topology builder — for someone who approaches every encounter differently.

    Pass a list of (zone1, zone2) tuples and a base stability.
    The body reshapes itself to the encounter.
    """
    bridges = {}
    for z1, z2 in zones:
        bridges[(z1, z2)] = FoldBridge(z1, z2, FinProb(stability, den))
    return BodyTopology(bridges=bridges)


# === TOPOLOGY REGISTRY ===

TOPOLOGIES = {
    "default": topology_default,
    "dominant": topology_dominant,
    "submissive": topology_submissive,
    "tender": topology_tender,
    "tease": topology_tease,
    "chaotic": topology_chaotic,
}


def get_topology(name: str) -> BodyTopology:
    """Get a preset topology by name."""
    factory = TOPOLOGIES.get(name, topology_default)
    return factory()


# === BUDGET PRESETS ===
# Budget determines session length. More budget = longer encounter.

BUDGET_PRESETS = {
    "quickie": 8,       # Fast, intense, collapses quickly
    "standard": 15,     # Normal session
    "marathon": 30,     # Long, evolving encounter
    "tantric": 50,      # Slow burn, high dimensionality throughout
    "edging": 12,       # Short budget but with recovery cycles planned
}


# === TEST ===

if __name__ == "__main__":
    print("=== VOID Body Topologies ===\n")
    for name, factory in TOPOLOGIES.items():
        topo = factory()
        bridge_names = [f"{b.zone1}↔{b.zone2}" for b in topo.bridges.values()]
        print(f"{name}: {len(topo.bridges)} bridges")
        print(f"  Bridges: {', '.join(bridge_names)}")
        print(f"  Fold energy: {topo.fold_energy}")
        print()

    # Shapeshifter demo
    custom = topology_shapeshifter([
        ("mouth", "worship"),
        ("hands", "devotion"),
        ("breath", "prayer"),
        ("eyes", "ecstasy"),
    ], stability=1, den=3)
    print(f"shapeshifter (custom): {len(custom.bridges)} bridges")
    bridge_names = [f"{b.zone1}↔{b.zone2}" for b in custom.bridges.values()]
    print(f"  Bridges: {', '.join(bridge_names)}")
