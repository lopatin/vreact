import { useReducer, useState, useEffect } from "react";
import { invariant, type int } from "vreact/spec";
import { type Card, initialBoard, wellFormed, allCards, findCard } from "./model";
import { boardReducer } from "./reducer";
import { ColumnView } from "./components/ColumnView";
import { AddCardForm } from "./components/AddCardForm";
import { Stats } from "./components/Stats";
import { WipControl } from "./components/WipControl";
import { Details } from "./components/Details";

const MAX_QUERY = 40;

export function App() {
  const [board, dispatch] = useReducer(boardReducer, initialBoard);
  const [query, setQuery] = useState<string>("");
  const [selected, setSelected] = useState<int | null>(null);
  const [notice, setNotice] = useState<string | null>(null);
  invariant(wellFormed(board));
  invariant(query.length <= MAX_QUERY);
  invariant(selected === null || allCards(board).some((c) => c.id === selected));

  // auto-dismiss the notice (a timer callback: runs later, against whatever the state is then)
  useEffect(() => {
    const t = setTimeout(() => setNotice(null), 2500);
    return () => clearTimeout(t);
  }, [notice]);

  const todo = board.todo.filter((c) => query.length === 0 || c.title.includes(query));
  const doing = board.doing.filter((c) => query.length === 0 || c.title.includes(query));
  const done = board.done.filter((c) => query.length === 0 || c.title.includes(query));
  const points = allCards(board).reduce((s: int, c: Card) => s + c.points, 0);
  const current = selected === null ? null : findCard(board, selected);

  return (
    <div className="app">
      <header>
        <h1>Verified Kanban</h1>
        <Stats todo={board.todo.length} doing={board.doing.length} done={board.done.length} points={points} />
        <WipControl
          limit={board.wipLimit}
          inProgress={board.doing.length}
          onChange={(n) => dispatch({ kind: "setWip", limit: n })}
        />
      </header>
      <AddCardForm
        onAdd={(title, pts) => {
          dispatch({ kind: "add", title, points: pts });
          setNotice(`Added “${title}”`);
        }}
      />
      <input
        className="filter"
        value={query}
        placeholder="Filter cards…"
        onChange={(e) => {
          if (e.target.value.length <= MAX_QUERY) setQuery(e.target.value);
        }}
      />
      {notice !== null && <p className="notice">{notice}</p>}
      <main className="columns">
        <ColumnView col="todo" title="To do" cards={todo} limit={null} selected={selected}
          onMove={(id, to) => dispatch({ kind: "move", id, to })}
          onDelete={(id) => { dispatch({ kind: "delete", id }); if (selected === id) setSelected(null); }}
          onSelect={(id) => setSelected(id)} />
        <ColumnView col="doing" title="Doing" cards={doing} limit={board.wipLimit} selected={selected}
          onMove={(id, to) => dispatch({ kind: "move", id, to })}
          onDelete={(id) => { dispatch({ kind: "delete", id }); if (selected === id) setSelected(null); }}
          onSelect={(id) => setSelected(id)} />
        <ColumnView col="done" title="Done" cards={done} limit={null} selected={selected}
          onMove={(id, to) => dispatch({ kind: "move", id, to })}
          onDelete={(id) => { dispatch({ kind: "delete", id }); if (selected === id) setSelected(null); }}
          onSelect={(id) => setSelected(id)} />
      </main>
      {current !== null && <Details card={current} onClose={() => setSelected(null)} />}
    </div>
  );
}
