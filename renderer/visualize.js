async function init() {
  const file = 'examples/Projection1.ast.json';
  const data = await fetch(file).then(r => r.json());
  renderGraph(data);
}

function renderGraph(ast) {
  const width = 900;
  const height = 600;
  const svg = d3.select('#viz')
    .append('svg')
    .attr('viewBox', `0 0 ${width} ${height}`)
    .attr('width', width)
    .attr('height', height)
    .call(d3.zoom().on('zoom', (event) => {
      inner.attr('transform', event.transform);
    }));

  const inner = svg.append('g');

  const epsilon = ast.functor.epsilon;
  const metric = ast.metric ? ast.metric.name : ast.functor.metric;
  d3.select('#metric').text(`Metric: ${metric}, ε = ${epsilon}`);

  const defs = svg.append('defs');
  defs.append('marker')
    .attr('id', 'arrow')
    .attr('viewBox', '0 -5 10 10')
    .attr('refX', 10)
    .attr('refY', 0)
    .attr('markerWidth', 6)
    .attr('markerHeight', 6)
    .attr('orient', 'auto')
    .append('path')
    .attr('d', 'M0,-5L10,0L0,5')
    .attr('fill', '#333');

  const categoryGap = 300;
  const objectGap = 80;
  const objectPos = {};

  ast.categories.forEach((cat, i) => {
    const x = 100 + i * categoryGap;
    inner.append('text')
      .attr('x', x)
      .attr('y', 40)
      .attr('text-anchor', 'middle')
      .attr('class', 'category-label')
      .text(cat.name);

    cat.objects.forEach((obj, j) => {
      const y = 100 + j * objectGap;
      objectPos[`${cat.name}:${obj}`] = { x, y };
      inner.append('circle')
        .attr('cx', x)
        .attr('cy', y)
        .attr('r', 20)
        .attr('class', 'object')
        .append('title').text(obj);
      inner.append('text')
        .attr('x', x)
        .attr('y', y + 35)
        .attr('text-anchor', 'middle')
        .text(obj);
    });
  });

  // Draw morphisms
  ast.categories.forEach((cat) => {
    cat.morphisms.forEach(m => {
      const from = objectPos[`${cat.name}:${m.from}`];
      const to = objectPos[`${cat.name}:${m.to}`];
      if (!from || !to) return;
      const path = inner.append('path')
        .attr('d', `M${from.x},${from.y} L${to.x},${to.y}`)
        .attr('class', 'morphism')
        .attr('marker-end', 'url(#arrow)');
      if (m.delta !== undefined && m.delta > epsilon) {
        path.attr('stroke', 'red').attr('stroke-dasharray', '4 2');
      }
      path.append('title').text(m.name + (m.delta !== undefined ? ` (δ=${m.delta})` : ''));
    });
  });

  const F = ast.functor;

  // Functor object_map
  Object.entries(F.object_map || {}).forEach(([src, dst]) => {
    const start = objectPos[`${F.from}:${src}`];
    const end = objectPos[`${F.to}:${dst}`];
    if (!start || !end) return;
    const midX = (start.x + end.x) / 2;
    const pathData = `M${start.x},${start.y} Q${midX},${start.y - 60} ${end.x},${end.y}`;
    inner.append('path')
      .attr('d', pathData)
      .attr('class', 'functor')
      .attr('marker-end', 'url(#arrow)')
      .append('title').text(`${src} → ${dst}`);
    inner.append('text')
      .attr('x', midX)
      .attr('y', start.y - 65)
      .attr('text-anchor', 'middle')
      .attr('class', 'functor-label')
      .text(`ε=${epsilon} ${metric}`);
  });

  // Functor morphism_map
  Object.entries(F.morphism_map || {}).forEach(([srcM, dstM]) => {
    const srcCat = ast.categories.find(c => c.name === F.from);
    const dstCat = ast.categories.find(c => c.name === F.to);
    if (!srcCat || !dstCat) return;
    const srcMorph = srcCat.morphisms.find(m => m.name === srcM);
    const dstMorph = dstCat.morphisms.find(m => m.name === dstM);
    if (!srcMorph || !dstMorph) return;
    const s1 = objectPos[`${F.from}:${srcMorph.from}`];
    const s2 = objectPos[`${F.from}:${srcMorph.to}`];
    const d1 = objectPos[`${F.to}:${dstMorph.from}`];
    const d2 = objectPos[`${F.to}:${dstMorph.to}`];
    const start = { x: (s1.x + s2.x) / 2, y: (s1.y + s2.y) / 2 };
    const end = { x: (d1.x + d2.x) / 2, y: (d1.y + d2.y) / 2 };
    const midX = (start.x + end.x) / 2;
    const pathData = `M${start.x},${start.y} Q${midX},${start.y - 60} ${end.x},${end.y}`;
    inner.append('path')
      .attr('d', pathData)
      .attr('class', 'functor')
      .attr('marker-end', 'url(#arrow)')
      .append('title').text(`${srcM} → ${dstM}`);
    inner.append('text')
      .attr('x', midX)
      .attr('y', start.y - 65)
      .attr('text-anchor', 'middle')
      .attr('class', 'functor-label')
      .text(`ε=${epsilon} ${metric}`);
  });
}

init();
