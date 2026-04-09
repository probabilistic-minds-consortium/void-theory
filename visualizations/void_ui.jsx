import { useState, useEffect, useRef } from "react";

const API = "http://localhost:8070";

// === VOID STATE VISUALIZATION ===

function BudgetBar({ budget, maxBudget = 20 }) {
  const pct = Math.max(0, (budget / maxBudget) * 100);
  const color = budget <= 2 ? "#ff1744" : budget <= 5 ? "#ff9100" : "#e0e0e0";
  return (
    <div style={{ marginBottom: 8 }}>
      <div style={{ display: "flex", justifyContent: "space-between", fontSize: 11, color: "#888", marginBottom: 2 }}>
        <span>BUDGET</span>
        <span>{budget}</span>
      </div>
      <div style={{ height: 4, background: "#1a1a1a", borderRadius: 2 }}>
        <div style={{ height: "100%", width: `${pct}%`, background: color, borderRadius: 2, transition: "all 0.5s ease" }} />
      </div>
    </div>
  );
}

function HeatBar({ heat }) {
  const segments = Math.min(20, heat);
  return (
    <div style={{ marginBottom: 8 }}>
      <div style={{ display: "flex", justifyContent: "space-between", fontSize: 11, color: "#888", marginBottom: 2 }}>
        <span>HEAT</span>
        <span>{heat}</span>
      </div>
      <div style={{ display: "flex", gap: 1, height: 4 }}>
        {Array.from({ length: 20 }, (_, i) => (
          <div
            key={i}
            style={{
              flex: 1,
              height: "100%",
              borderRadius: 1,
              background: i < segments
                ? `hsl(${Math.max(0, 30 - i * 1.5)}, 100%, ${Math.max(40, 60 - i * 1.5)}%)`
                : "#1a1a1a",
              transition: "all 0.3s ease",
            }}
          />
        ))}
      </div>
    </div>
  );
}

function DimensionDisplay({ dimensions }) {
  return (
    <div style={{ marginBottom: 12 }}>
      <div style={{ fontSize: 11, color: "#888", marginBottom: 4 }}>DIMENSIONS</div>
      <div style={{ display: "flex", gap: 6 }}>
        {[1, 2, 3].map((d) => (
          <div
            key={d}
            style={{
              width: 28,
              height: 28,
              borderRadius: "50%",
              display: "flex",
              alignItems: "center",
              justifyContent: "center",
              fontSize: 13,
              fontWeight: 600,
              background: d <= dimensions ? (d === 1 ? "#ff1744" : d === 2 ? "#ff9100" : "#333") : "#0a0a0a",
              color: d <= dimensions ? (d <= 2 ? "#000" : "#ccc") : "#333",
              border: d <= dimensions ? "none" : "1px solid #222",
              transition: "all 0.5s ease",
            }}
          >
            {d}D
          </div>
        ))}
      </div>
    </div>
  );
}

function BridgeMap({ bridges, position }) {
  return (
    <div style={{ marginBottom: 12 }}>
      <div style={{ fontSize: 11, color: "#888", marginBottom: 6 }}>TOPOLOGY</div>
      <div style={{ display: "flex", flexWrap: "wrap", gap: 4 }}>
        {Object.entries(bridges).map(([name, b]) => {
          const isCollapsed = !b.alive;
          const isLocked = b.locked;
          const isHot = b.heat_signature > 2;
          const isFragile = b.stability < 0.5 && b.alive;
          const isCurrent = name.includes(position);

          let bg = "#111";
          let border = "1px solid #222";
          let textColor = "#666";

          if (isCollapsed) {
            bg = "#0a0a0a";
            border = "1px solid #1a1a1a";
            textColor = "#333";
          } else if (isLocked) {
            bg = "#1a0a0a";
            border = "1px solid #331111";
            textColor = "#663333";
          } else if (isHot) {
            bg = "#1a1000";
            border = "1px solid #332200";
            textColor = "#cc8800";
          } else if (isFragile) {
            bg = "#1a0000";
            border = "1px solid #330000";
            textColor = "#aa3333";
          } else if (isCurrent) {
            bg = "#111";
            border = "1px solid #444";
            textColor = "#ccc";
          }

          return (
            <div
              key={name}
              style={{
                padding: "3px 8px",
                borderRadius: 3,
                background: bg,
                border,
                fontSize: 10,
                color: textColor,
                fontFamily: "monospace",
                opacity: isCollapsed ? 0.4 : 1,
                transition: "all 0.3s ease",
              }}
              title={
                isCollapsed ? "COLLAPSED" :
                isLocked ? `LOCKED (requires: ${(b.requires || []).join(", ")})` :
                `stability: ${(b.stability * 100).toFixed(0)}% | crossed: ${b.cross_count}x`
              }
            >
              {isLocked && "🔒 "}
              {isCollapsed && "✕ "}
              {isHot && "🔥 "}
              {name.replace("-", " ↔ ")}
            </div>
          );
        })}
      </div>
    </div>
  );
}

function TrajectoryLine({ trajectory }) {
  if (!trajectory || trajectory.length === 0) return null;
  const recent = trajectory.slice(-8);
  return (
    <div style={{ marginBottom: 12 }}>
      <div style={{ fontSize: 11, color: "#888", marginBottom: 4 }}>PATH</div>
      <div style={{ fontSize: 11, color: "#555", fontFamily: "monospace", wordBreak: "break-all" }}>
        {recent.join(" → ")}
      </div>
    </div>
  );
}

// === ZONE SELECTOR ===

function ZoneSelector({ bridges, onSelect, disabled }) {
  const zones = new Set();
  Object.values(bridges).forEach((b) => {
    const parts = Object.keys(bridges).find((k) => bridges[k] === b);
  });

  const available = Object.entries(bridges)
    .filter(([_, b]) => b.alive)
    .map(([name, b]) => {
      const [z1, z2] = name.split("-");
      return { name, z1, z2, locked: b.locked };
    });

  return (
    <div style={{ display: "flex", flexWrap: "wrap", gap: 4, marginBottom: 8 }}>
      {available.map(({ name, z1, z2, locked }) => (
        <button
          key={name}
          onClick={() => onSelect(z2)}
          disabled={disabled}
          style={{
            padding: "4px 10px",
            borderRadius: 3,
            border: locked ? "1px solid #331111" : "1px solid #333",
            background: locked ? "#1a0a0a" : "#111",
            color: locked ? "#663333" : "#aaa",
            fontSize: 11,
            fontFamily: "monospace",
            cursor: disabled ? "not-allowed" : "pointer",
            opacity: disabled ? 0.5 : 1,
          }}
        >
          {locked ? "🔒 " : "→ "}{z2}
        </button>
      ))}
    </div>
  );
}

// === CHAT MESSAGE ===

function ChatMessage({ role, content, locked, requires }) {
  const isUser = role === "user";
  return (
    <div style={{ marginBottom: 12, display: "flex", flexDirection: "column", alignItems: isUser ? "flex-end" : "flex-start" }}>
      {locked && (
        <div style={{ fontSize: 10, color: "#663333", fontFamily: "monospace", marginBottom: 2, padding: "2px 8px", background: "#1a0a0a", borderRadius: 3, border: "1px solid #331111" }}>
          🔒 locked — requires: {(requires || []).join(", ")}
        </div>
      )}
      <div
        style={{
          maxWidth: "80%",
          padding: "8px 12px",
          borderRadius: isUser ? "12px 12px 2px 12px" : "12px 12px 12px 2px",
          background: isUser ? "#1a1a2e" : "#111",
          border: isUser ? "1px solid #2a2a4e" : "1px solid #222",
          color: isUser ? "#ccc" : "#999",
          fontSize: 14,
          lineHeight: 1.5,
          whiteSpace: "pre-wrap",
        }}
      >
        {content}
      </div>
    </div>
  );
}

// === MAIN APP ===

export default function VoidUI() {
  const [sessionId, setSessionId] = useState(null);
  const [state, setState] = useState(null);
  const [messages, setMessages] = useState([]);
  const [input, setInput] = useState("");
  const [selectedZone, setSelectedZone] = useState(null);
  const [loading, setLoading] = useState(false);
  const [topology, setTopology] = useState("default");
  const [budget, setBudget] = useState(15);
  const chatRef = useRef(null);

  const startSession = async () => {
    try {
      const res = await fetch(`${API}/session/start`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ topology, budget, provider: "ollama" }),
      });
      const data = await res.json();
      setSessionId(data.session_id);
      setState(data.state);
      setMessages([]);
      setSelectedZone(null);
    } catch (e) {
      setMessages([{ role: "system", content: `Connection error: ${e.message}. Is the server running?` }]);
    }
  };

  const sendMessage = async () => {
    if (!input.trim() || !sessionId) return;
    const userMsg = input.trim();
    setInput("");
    setMessages((prev) => [...prev, { role: "user", content: userMsg }]);
    setLoading(true);

    try {
      const res = await fetch(`${API}/session/${sessionId}/chat`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ message: userMsg, zone: selectedZone }),
      });
      const data = await res.json();

      if (data.detail) {
        setMessages((prev) => [...prev, { role: "system", content: data.detail }]);
      } else {
        const isLocked = data.interaction?.locked;
        setMessages((prev) => [...prev, {
          role: "assistant",
          content: data.response,
          locked: isLocked,
          requires: data.interaction?.requires,
        }]);
        setState(data.state);
      }
    } catch (e) {
      setMessages((prev) => [...prev, { role: "system", content: `Error: ${e.message}` }]);
    }
    setSelectedZone(null);
    setLoading(false);
  };

  const doRecovery = async () => {
    if (!sessionId) return;
    try {
      const res = await fetch(`${API}/session/${sessionId}/recovery`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ ticks: 3 }),
      });
      const data = await res.json();
      setState(data.state);
      setMessages((prev) => [...prev, {
        role: "system",
        content: `recovery: +${data.recovery.recovered_budget} budget. heat remains: ${data.recovery.heat_remains}. breath.`,
      }]);
    } catch (e) {}
  };

  useEffect(() => {
    if (chatRef.current) {
      chatRef.current.scrollTop = chatRef.current.scrollHeight;
    }
  }, [messages]);

  // === LOBBY ===
  if (!sessionId) {
    return (
      <div style={{ minHeight: "100vh", background: "#000", color: "#ccc", display: "flex", alignItems: "center", justifyContent: "center", fontFamily: "'Inter', system-ui, sans-serif" }}>
        <div style={{ width: 360, textAlign: "center" }}>
          <div style={{ fontSize: 32, fontWeight: 200, letterSpacing: 8, marginBottom: 4, color: "#fff" }}>VOID</div>
          <div style={{ fontSize: 11, color: "#444", letterSpacing: 3, marginBottom: 40 }}>EROTIC AI</div>

          <div style={{ textAlign: "left", marginBottom: 20 }}>
            <div style={{ fontSize: 11, color: "#555", marginBottom: 6 }}>TOPOLOGY</div>
            <div style={{ display: "flex", flexWrap: "wrap", gap: 6 }}>
              {["default", "dominant", "submissive", "tender", "tease", "chaotic"].map((t) => (
                <button
                  key={t}
                  onClick={() => setTopology(t)}
                  style={{
                    padding: "6px 14px",
                    borderRadius: 3,
                    border: topology === t ? "1px solid #555" : "1px solid #222",
                    background: topology === t ? "#1a1a1a" : "#0a0a0a",
                    color: topology === t ? "#ccc" : "#555",
                    fontSize: 12,
                    fontFamily: "monospace",
                    cursor: "pointer",
                    transition: "all 0.2s ease",
                  }}
                >
                  {t}
                </button>
              ))}
            </div>
          </div>

          <div style={{ textAlign: "left", marginBottom: 30 }}>
            <div style={{ fontSize: 11, color: "#555", marginBottom: 6 }}>BUDGET: {budget}</div>
            <input
              type="range"
              min={5}
              max={50}
              value={budget}
              onChange={(e) => setBudget(parseInt(e.target.value))}
              style={{ width: "100%", accentColor: "#555" }}
            />
            <div style={{ display: "flex", justifyContent: "space-between", fontSize: 10, color: "#333" }}>
              <span>quickie</span>
              <span>standard</span>
              <span>marathon</span>
              <span>tantric</span>
            </div>
          </div>

          <button
            onClick={startSession}
            style={{
              width: "100%",
              padding: "12px 0",
              borderRadius: 3,
              border: "1px solid #333",
              background: "#111",
              color: "#ccc",
              fontSize: 13,
              letterSpacing: 2,
              cursor: "pointer",
              transition: "all 0.2s ease",
            }}
            onMouseEnter={(e) => { e.target.style.background = "#1a1a1a"; e.target.style.borderColor = "#555"; }}
            onMouseLeave={(e) => { e.target.style.background = "#111"; e.target.style.borderColor = "#333"; }}
          >
            ENTER
          </button>
        </div>
      </div>
    );
  }

  // === SESSION ===
  return (
    <div style={{ minHeight: "100vh", background: "#000", color: "#ccc", fontFamily: "'Inter', system-ui, sans-serif", display: "flex" }}>
      {/* SIDEBAR — state */}
      <div style={{ width: 260, borderRight: "1px solid #111", padding: 16, flexShrink: 0, overflowY: "auto" }}>
        <div style={{ fontSize: 18, fontWeight: 200, letterSpacing: 4, marginBottom: 4, color: "#fff" }}>VOID</div>
        <div style={{ fontSize: 9, color: "#333", letterSpacing: 2, marginBottom: 20 }}>{sessionId}</div>

        {state && (
          <>
            <BudgetBar budget={state.budget} maxBudget={budget} />
            <HeatBar heat={state.heat} />
            <DimensionDisplay dimensions={state.dimensions} />
            <BridgeMap bridges={state.bridges} position={state.position} />
            <TrajectoryLine trajectory={state.trajectory} />

            <div style={{ fontSize: 10, color: "#333", fontFamily: "monospace", marginBottom: 8 }}>
              position: {state.position} | turn: {state.turn_count} | curvature: {(state.curvature * 100).toFixed(0)}%
            </div>

            <button
              onClick={doRecovery}
              style={{
                width: "100%",
                padding: "8px 0",
                borderRadius: 3,
                border: "1px solid #222",
                background: "#0a0a0a",
                color: "#555",
                fontSize: 11,
                letterSpacing: 1,
                cursor: "pointer",
                marginBottom: 8,
              }}
            >
              RECOVERY
            </button>

            <button
              onClick={() => { setSessionId(null); setState(null); setMessages([]); }}
              style={{
                width: "100%",
                padding: "8px 0",
                borderRadius: 3,
                border: "1px solid #1a0000",
                background: "#0a0000",
                color: "#553333",
                fontSize: 11,
                letterSpacing: 1,
                cursor: "pointer",
              }}
            >
              END SESSION
            </button>
          </>
        )}
      </div>

      {/* MAIN — chat */}
      <div style={{ flex: 1, display: "flex", flexDirection: "column" }}>
        {/* Messages */}
        <div ref={chatRef} style={{ flex: 1, overflowY: "auto", padding: "20px 24px" }}>
          {messages.length === 0 && (
            <div style={{ color: "#222", fontSize: 13, textAlign: "center", marginTop: 80 }}>
              every act of knowing costs something
            </div>
          )}
          {messages.map((msg, i) => (
            <ChatMessage key={i} role={msg.role} content={msg.content} locked={msg.locked} requires={msg.requires} />
          ))}
          {loading && (
            <div style={{ color: "#333", fontSize: 12, fontStyle: "italic" }}>...</div>
          )}
        </div>

        {/* Zone selector + input */}
        <div style={{ borderTop: "1px solid #111", padding: "12px 24px" }}>
          {state && (
            <div style={{ marginBottom: 6 }}>
              <div style={{ fontSize: 10, color: "#444", marginBottom: 4 }}>
                {selectedZone ? `→ ${selectedZone}` : "select zone (optional)"}
              </div>
              <ZoneSelector
                bridges={state.bridges}
                onSelect={(z) => setSelectedZone(selectedZone === z ? null : z)}
                disabled={loading || state.is_frozen}
              />
            </div>
          )}
          <div style={{ display: "flex", gap: 8 }}>
            <input
              type="text"
              value={input}
              onChange={(e) => setInput(e.target.value)}
              onKeyDown={(e) => e.key === "Enter" && !e.shiftKey && sendMessage()}
              placeholder={state?.is_frozen ? "frozen. recovery or end." : "..."}
              disabled={loading}
              style={{
                flex: 1,
                padding: "10px 14px",
                borderRadius: 3,
                border: "1px solid #222",
                background: "#0a0a0a",
                color: "#ccc",
                fontSize: 14,
                fontFamily: "'Inter', system-ui, sans-serif",
                outline: "none",
              }}
            />
            <button
              onClick={sendMessage}
              disabled={loading || !input.trim()}
              style={{
                padding: "10px 20px",
                borderRadius: 3,
                border: "1px solid #222",
                background: "#111",
                color: "#666",
                fontSize: 13,
                cursor: loading ? "not-allowed" : "pointer",
              }}
            >
              ↵
            </button>
          </div>
        </div>
      </div>
    </div>
  );
}
