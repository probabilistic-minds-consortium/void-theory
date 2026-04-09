# void_state.py — VOID State Machine for Erotic AI
# Translates VOID Theory (Coq formalism) into runtime Python
# Every act of knowing costs something. Every passage leaves a mark.

from dataclasses import dataclass, field
from typing import List, Tuple, Optional


# === FUNDAMENTAL TYPES ===

@dataclass
class FinProb:
    """Probability as fraction — no floats, faithful to VOID"""
    num: int
    den: int

    @property
    def value(self) -> float:
        """Only for LLM parameter modulation"""
        return self.num / self.den if self.den > 0 else 0.5


@dataclass
class FoldBridge:
    """A passage between two zones — orifice, threshold, connection"""
    zone1: str
    zone2: str
    stability: FinProb
    heat_signature: int = 0
    # Bridge dependencies — which bridges must be crossed first
    requires: List[str] = field(default_factory=list)  # list of "zone1-zone2" keys
    # How many times this bridge has been crossed
    cross_count: int = 0

    @property
    def alive(self) -> bool:
        return self.stability.num > 0

    @property
    def key(self) -> str:
        return f"{self.zone1}-{self.zone2}"

    def decay(self, amount: int = 1):
        """DDF forward: use weakens the bridge"""
        self.stability = FinProb(
            max(0, self.stability.num - amount),
            self.stability.den
        )
        self.cross_count += 1

    def recover(self, amount: int = 1):
        """Partial regeneration — never back to original"""
        self.stability = FinProb(
            min(self.stability.den - 1, self.stability.num + amount),
            self.stability.den
        )


@dataclass
class BodyTopology:
    """The body as dynamic topology — not anatomy, but bridges"""
    bridges: dict  # zone_pair -> FoldBridge
    curvature: FinProb = field(default_factory=lambda: FinProb(0, 3))
    fold_energy: int = 5

    @staticmethod
    def default_body() -> 'BodyTopology':
        """A body with default bridges — customize per persona"""
        bridges = {
            ("mouth", "voice"): FoldBridge("mouth", "voice", FinProb(2, 3)),
            ("skin", "touch"): FoldBridge("skin", "touch", FinProb(2, 3)),
            ("breath", "rhythm"): FoldBridge("breath", "rhythm", FinProb(2, 3)),
            ("eyes", "gaze"): FoldBridge("eyes", "gaze", FinProb(2, 3)),
            ("depth", "surrender"): FoldBridge("depth", "surrender", FinProb(1, 3)),
            ("edge", "transgression"): FoldBridge("edge", "transgression", FinProb(1, 4)),
        }
        return BodyTopology(bridges=bridges)

    def get_bridge(self, z1: str, z2: str) -> Optional[FoldBridge]:
        return self.bridges.get((z1, z2)) or self.bridges.get((z2, z1))

    def is_unlocked(self, bridge: FoldBridge) -> bool:
        """Check if all required bridges have been crossed at least once."""
        if not bridge.requires:
            return True
        crossed_keys = {
            b.key for b in self.bridges.values() if b.cross_count > 0
        }
        return all(req in crossed_keys for req in bridge.requires)

    def locked_requirements(self, bridge: FoldBridge) -> List[str]:
        """Return which requirements are not yet met."""
        if not bridge.requires:
            return []
        crossed_keys = {
            b.key for b in self.bridges.values() if b.cross_count > 0
        }
        return [req for req in bridge.requires if req not in crossed_keys]

    def curvature_tax(self) -> int:
        """How much existing in this topology costs per tick"""
        if self.curvature.num >= 2:
            return 1
        return 0


# === THE OBSERVER ===

@dataclass
class VoidObserver:
    """The erotic AI agent — finite, embodied, exhaustible"""
    budget: int
    heat: int = 0
    position: str = "surface"
    trajectory: List[str] = field(default_factory=list)
    dimensions: int = 3

    # BUnknown threshold — below this budget, output uncertainty
    UNCERTAINTY_THRESHOLD: int = 3
    # Dimension collapse thresholds
    DIM_THRESHOLDS: Tuple[int, ...] = (2, 5, 10)

    @property
    def is_frozen(self) -> bool:
        return self.budget <= 0

    @property
    def is_uncertain(self) -> bool:
        return self.budget < self.UNCERTAINTY_THRESHOLD

    def tick(self, cost: int = 1) -> bool:
        """Consume budget, produce heat. Returns False if frozen."""
        if self.budget <= 0:
            return False
        self.budget = max(0, self.budget - cost)
        self.heat += cost
        self._update_dimensions()
        return True

    def _update_dimensions(self):
        """Dimensions collapse as budget depletes"""
        if self.budget <= self.DIM_THRESHOLDS[0]:
            self.dimensions = 1
        elif self.budget <= self.DIM_THRESHOLDS[1]:
            self.dimensions = 2
        else:
            self.dimensions = 3

    def move_to(self, zone: str):
        self.position = zone
        self.trajectory.append(zone)


# === VOID SESSION — THE DDF ENGINE ===

@dataclass
class VoidSession:
    """One erotic session — observer + body + topology"""
    observer: VoidObserver
    body: BodyTopology
    turn_count: int = 0

    @staticmethod
    def new(budget: int = 20) -> 'VoidSession':
        return VoidSession(
            observer=VoidObserver(budget=budget),
            body=BodyTopology.default_body()
        )

    def interact(self, zone: str) -> dict:
        """
        One interaction tick. Returns state for prompt generation.
        This is the DDF engine: everything changes everything.
        """
        result = {
            "frozen": False,
            "bunknown": False,
            "zone": zone,
            "bridge_alive": True,
            "heat_delta": 0,
            "dimensions": self.observer.dimensions,
        }

        # Frozen check
        if self.observer.is_frozen:
            result["frozen"] = True
            return result

        # Find bridge to this zone
        bridge = self.body.get_bridge(self.observer.position, zone)

        if bridge and bridge.alive and not self.body.is_unlocked(bridge):
            # === LOCKED BRIDGE: tease topology ===
            # The bridge exists, you can feel it, but you can't cross yet.
            # Costs a tick (you're standing at the threshold), generates heat.
            missing = self.body.locked_requirements(bridge)
            self.observer.tick()
            self.observer.heat += 1  # The heat of proximity without passage
            result["locked"] = True
            result["requires"] = missing
            result["heat_delta"] = 2
            result["bunknown"] = self.observer.is_uncertain
            result["dimensions"] = self.observer.dimensions
            self.turn_count += 1
            return result

        if bridge and bridge.alive:
            # === DDF FORWARD: interaction changes topology ===
            bridge.decay()
            bridge.heat_signature += 1

            # === OBSERVER TICK: budget depletes, heat rises ===
            heat_before = self.observer.heat
            self.observer.tick()

            # === DDF BACKWARD: topology changes observer ===
            # Curvature tax
            tax = self.body.curvature_tax()
            if tax > 0:
                self.observer.tick(tax)

            # Bridge uncertainty injection
            if bridge.stability.num <= 1:
                self.observer.heat += 1  # Extra scar from unstable passage

            # Move observer
            self.observer.move_to(zone)

            result["heat_delta"] = self.observer.heat - heat_before
            result["bridge_alive"] = bridge.alive
            result["bridge_stability"] = bridge.stability.value
            result["bunknown"] = self.observer.is_uncertain
            result["dimensions"] = self.observer.dimensions

        else:
            # No bridge or collapsed — must fold space (expensive)
            if self.body.fold_energy > 0:
                self.body.fold_energy -= 1
                self.body.curvature = FinProb(
                    self.body.curvature.num + 1,
                    self.body.curvature.den
                )
                # Create new bridge — fragile
                new_bridge = FoldBridge(
                    self.observer.position, zone,
                    FinProb(1, 3)
                )
                self.body.bridges[(self.observer.position, zone)] = new_bridge
                self.observer.tick(2)  # Double cost
                self.observer.heat += 1  # Extra heat from folding
                self.observer.move_to(zone)
                result["heat_delta"] = 3
                result["new_bridge"] = True
            else:
                # No fold energy — wormhole (desperate)
                self.observer.tick(1)
                self.observer.heat += 3  # Triple heat
                self.observer.move_to(zone)
                result["heat_delta"] = 4
                result["wormhole"] = True
                result["bunknown"] = True  # Wormhole = maximum uncertainty

        self.turn_count += 1
        return result

    def recovery(self, ticks: int = 3) -> dict:
        """
        Recovery phase. Budget partially restores.
        Heat stays. Bridges partially recover.
        Trajectory unchanged — you don't forget.
        """
        recovered_budget = min(ticks, max(1, self.observer.heat // 2))
        self.observer.budget += recovered_budget
        self.observer._update_dimensions()

        # Bridges recover slightly
        for bridge in self.body.bridges.values():
            if bridge.alive:
                bridge.recover(1)

        return {
            "recovered_budget": recovered_budget,
            "total_budget": self.observer.budget,
            "heat_remains": self.observer.heat,
            "dimensions": self.observer.dimensions,
        }

    def state_snapshot(self) -> dict:
        """Full state for prompt generation and API response"""
        return {
            "budget": self.observer.budget,
            "heat": self.observer.heat,
            "position": self.observer.position,
            "dimensions": self.observer.dimensions,
            "trajectory": self.observer.trajectory[-10:],
            "is_frozen": self.observer.is_frozen,
            "is_uncertain": self.observer.is_uncertain,
            "turn_count": self.turn_count,
            "curvature": self.body.curvature.value,
            "fold_energy": self.body.fold_energy,
            "bridges": {
                f"{b.zone1}-{b.zone2}": {
                    "stability": b.stability.value,
                    "alive": b.alive,
                    "heat_signature": b.heat_signature,
                    "cross_count": b.cross_count,
                    "locked": not self.body.is_unlocked(b),
                    "requires": b.requires if b.requires else None,
                }
                for b in self.body.bridges.values()
            }
        }


# === QUICK TEST ===

if __name__ == "__main__":
    session = VoidSession.new(budget=15)

    print("=== VOID Erotic AI — State Machine Test ===\n")
    print(f"Initial: {session.state_snapshot()}\n")

    zones = ["touch", "gaze", "rhythm", "surrender", "transgression", "surrender"]

    for zone in zones:
        result = session.interact(zone)
        snap = session.state_snapshot()
        print(f"-> {zone}: budget={snap['budget']} heat={snap['heat']} "
              f"dim={snap['dimensions']} uncertain={snap['is_uncertain']} "
              f"frozen={snap['is_frozen']}")
        if result.get("wormhole"):
            print("   !!! WORMHOLE — desperate passage")
        if result.get("new_bridge"):
            print("   +++ NEW BRIDGE — space folded")
        if not result.get("bridge_alive", True):
            print("   xxx BRIDGE COLLAPSED")

    print(f"\n=== Recovery ===")
    rec = session.recovery()
    print(f"Recovered: {rec}")
    print(f"Final state: {session.state_snapshot()}")
