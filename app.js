(() => {
  "use strict";

  const $ = selector => document.querySelector(selector);
  const canvas = $("#sphere-canvas");
  const wrapper = $("#sphere-wrap");
  const chooseScreen = $("#choose-screen");
  const bubbleScreen = $("#bubble-screen");
  const bubbleGrid = $("#bubble-grid");
  const bubbleCounter = $("#bubble-counter");
  const sphereScreen = $("#sphere-screen");
  const status = $("#status-message");

  // ── 왁뿌볼 상수 ────────────────────────────────────────────
  const WAX_OUTER = 1;        // 왁스 바깥면 반지름
  const WAX_INNER = .952;     // 왁스 안쪽면 반지름 (두께 ≈ .048)
  const CLAY_RADIUS = .956;   // 점토 반지름 (왁스 안쪽보다 살짝 커서 틈이 안 보임)
  const BEVEL_DROP = .010;    // 금이 갈 때 모서리가 둥글게 내려앉는 깊이
  const KIND_CAP = 0;
  const KIND_WALL = 1;
  // 법선 종류: 윗면(구 방향) / 둥근 모서리 / 옆벽 / 아랫면
  const NORMAL_CAP = 0;
  const NORMAL_BEVEL = 1;
  const NORMAL_WALL = 2;
  const NORMAL_BOTTOM = 3;

  let renderer;
  let scene;
  let camera;
  let sphere;
  let ball = null;
  let raycaster;
  let audioContext = null;
  let audioNoiseBuffer = null;
  let rotationFrame = 0;
  let pointer = null;
  let velocityX = 0;
  let velocityY = 0;
  let previousFrame = 0;
  let poppedBubbleCount = 0;
  let totalBubbleCount = 0;
  let rotateMode = false;
  let photoDataUrl = null;
  let photoImage = null;
  let photoTexture = null;
  const PHOTO_KEY = "stress-off-photo";

  const smooth = (x, a, b) => {
    const t = Math.min(1, Math.max(0, (x - a) / (b - a)));
    return t * t * (3 - 2 * t);
  };

  function mulberry32(seed) {
    return () => {
      seed = seed + 0x6D2B79F5 | 0;
      let t = Math.imul(seed ^ seed >>> 15, 1 | seed);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }

  // 누른 자리 모양: 가운데는 쏙 들어가고, 바깥 고리는 살짝 부풀어 오름 (말랑한 점토)
  function dentShape(dot) {
    const angle = Math.acos(dot > 1 ? 1 : dot < -1 ? -1 : dot);
    if (angle > 1.7) return 0;
    const ring = angle - .9;
    return Math.exp(-angle * angle / .17) - .26 * Math.exp(-ring * ring / .09);
  }

  // 눌린 자국의 기울기(접선 방향 벡터)를 out에 더함 → 자국 음영 표현
  function addDentSlope(out, o, ux, uy, uz, cx, cy, cz, depth) {
    const dot = ux * cx + uy * cy + uz * cz;
    const angle = Math.acos(dot > 1 ? 1 : dot < -1 ? -1 : dot);
    if (angle > 1.7 || angle < 1e-4) return;
    const ring = angle - .9;
    const slope = -2 * angle / .17 * Math.exp(-angle * angle / .17)
      + .26 * 2 * ring / .09 * Math.exp(-ring * ring / .09);
    let tx = ux * dot - cx;
    let ty = uy * dot - cy;
    let tz = uz * dot - cz;
    const length = Math.hypot(tx, ty, tz);
    if (length < 1e-6) return;
    const s = depth * slope / length;
    out[o] += tx * s;
    out[o + 1] += ty * s;
    out[o + 2] += tz * s;
  }

  // 측지 구(geodesic sphere): 고유 정점 + 바깥을 향하는 삼각형
  function geodesic(THREE, frequency) {
    const vertices = [];
    const faces = [];
    const vertexIndices = new Map();
    const baseGeometry = new THREE.IcosahedronGeometry(1, 0);
    const basePositions = baseGeometry.getAttribute("position");
    const getVertexIndex = point => {
      const unit = point.clone().normalize();
      const key = `${unit.x.toFixed(6)},${unit.y.toFixed(6)},${unit.z.toFixed(6)}`;
      if (vertexIndices.has(key)) return vertexIndices.get(key);
      const index = vertices.push(unit) - 1;
      vertexIndices.set(key, index);
      return index;
    };
    for (let index = 0; index < basePositions.count; index += 3) {
      faces.push([
        getVertexIndex(new THREE.Vector3().fromBufferAttribute(basePositions, index)),
        getVertexIndex(new THREE.Vector3().fromBufferAttribute(basePositions, index + 1)),
        getVertexIndex(new THREE.Vector3().fromBufferAttribute(basePositions, index + 2))
      ]);
    }
    baseGeometry.dispose();
    const triangles = [];
    faces.forEach(([a, b, c]) => {
      const grid = [];
      for (let i = 0; i <= frequency; i++) {
        grid[i] = [];
        for (let j = 0; j <= frequency - i; j++) {
          const point = vertices[a].clone().multiplyScalar(frequency - i - j)
            .addScaledVector(vertices[b], i)
            .addScaledVector(vertices[c], j)
            .divideScalar(frequency);
          grid[i][j] = getVertexIndex(point);
        }
      }
      for (let i = 0; i < frequency; i++) {
        for (let j = 0; j < frequency - i; j++) {
          triangles.push([grid[i][j], grid[i + 1][j], grid[i][j + 1]]);
          if (j < frequency - i - 1) {
            triangles.push([grid[i + 1][j], grid[i + 1][j + 1], grid[i][j + 1]]);
          }
        }
      }
    });
    const ab = new THREE.Vector3();
    const ac = new THREE.Vector3();
    triangles.forEach(tri => {
      const [a, b, c] = tri.map(index => vertices[index]);
      ab.subVectors(b, a);
      ac.subVectors(c, a);
      if (ab.cross(ac).dot(a) < 0) {
        const swap = tri[1];
        tri[1] = tri[2];
        tri[2] = swap;
      }
    });
    return { vertices, triangles };
  }

  function buildSphere() {
    const THREE = window.THREE;
    const V = THREE.Vector3;
    const rand = mulberry32((Math.random() * 4294967296) >>> 0);

    // 1) 조각 씨앗: 측지 구 정점을 흔들어 불규칙한 보로노이 조각을 만듦
    const { vertices: seeds, triangles } = geodesic(THREE, 8);
    seeds.forEach(seed => {
      const tangent = new V(rand() * 2 - 1, rand() * 2 - 1, rand() * 2 - 1);
      tangent.addScaledVector(seed, -tangent.dot(seed));
      if (tangent.lengthSq() < 1e-6) return;
      seed.addScaledVector(tangent.normalize(), .01 + rand() * .036).normalize();
    });
    const corners = triangles.map(([a, b, c]) => seeds[a].clone().add(seeds[b]).add(seeds[c]).normalize());
    const incident = seeds.map(() => []);
    triangles.forEach((tri, t) => tri.forEach(vertex => incident[vertex].push(t)));

    const tangentBasis = normal => {
      const reference = Math.abs(normal.y) > .9 ? new V(1, 0, 0) : new V(0, 1, 0);
      const right = new V().crossVectors(reference, normal).normalize();
      const up = new V().crossVectors(normal, right);
      return [right, up];
    };
    const randomTangent = normal => {
      const [right, up] = tangentBasis(normal);
      const angle = rand() * Math.PI * 2;
      return right.multiplyScalar(Math.cos(angle)).addScaledVector(up, Math.sin(angle));
    };
    const warp = (vector, amount, offset) => vector.clone().add(new V(
      Math.sin(vector.y * 3.1 + vector.z * 1.7 + offset),
      Math.sin(vector.z * 2.7 + vector.x * 3.3 + offset * 1.3),
      Math.sin(vector.x * 3.7 + vector.y * 2.1 + offset * .7)
    ).multiplyScalar(amount)).normalize();
    const fibonacci = count => Array.from({ length: count }, (_, index) => {
      const y = 1 - 2 * (index + .5) / count;
      const radius = Math.sqrt(1 - y * y);
      const phi = index * 2.399963 + rand() * .3;
      const point = new V(Math.cos(phi) * radius, y, Math.sin(phi) * radius);
      return point.addScaledVector(randomTangent(point), Math.sqrt(4 * Math.PI / count) * .3 * rand()).normalize();
    });
    const nearest = (vector, list) => {
      let best = 0;
      let bestDot = -2;
      list.forEach((seed, index) => {
        const dot = vector.dot(seed);
        if (dot > bestDot) {
          bestDot = dot;
          best = index;
        }
      });
      return best;
    };
    const average = list => list.reduce((sum, vector) => sum.add(vector), new V()).normalize();

    // 2) 계층 묶음: 큰 덩어리(0) ⊃ 중간 덩어리(1) ⊃ 낱조각(2)
    const clusters = [];
    const makeCluster = (level, center) => {
      const cluster = {
        level,
        center,
        damage: 0,
        shown: 0,
        p: 0,
        q: 0,
        axis: randomTangent(center),
        drift: randomTangent(center),
        tilt: (rand() < .5 ? -1 : 1) * (.45 + rand() * .55),
        shrink: .8 + rand() * .4,
        tint: rand() * 2 - 1,
        push: new V(),
        matrix: new THREE.Matrix4()
      };
      clusters.push(cluster);
      return cluster;
    };
    const offsetA = rand() * 10;
    const offsetB = rand() * 10;
    const mediumSeeds = fibonacci(140);
    const coarseSeeds = fibonacci(30);
    const mediumMembers = mediumSeeds.map(() => []);
    seeds.forEach((seed, index) => mediumMembers[nearest(warp(seed, .14, offsetA), mediumSeeds)].push(index));
    const mediumGroups = mediumMembers
      .filter(members => members.length)
      .map(members => ({ members, center: average(members.map(index => seeds[index])) }));
    const coarseMembers = coarseSeeds.map(() => []);
    mediumGroups.forEach(group => coarseMembers[nearest(warp(group.center, .18, offsetB), coarseSeeds)].push(group));
    const cellChain = new Array(seeds.length);
    coarseMembers.forEach(groups => {
      if (!groups.length) return;
      const coarse = makeCluster(0, average(groups.flatMap(group => group.members.map(index => seeds[index]))));
      groups.forEach(group => {
        const medium = makeCluster(1, group.center);
        group.members.forEach(index => {
          cellChain[index] = [coarse, medium, null];
        });
      });
    });

    // 낱조각: 이웃 셀 1~3개를 무작위로 합쳐 모양이 제각각인 조각을 만듦
    const neighbors = seeds.map(() => new Set());
    triangles.forEach(([a, b, c]) => {
      neighbors[a].add(b).add(c);
      neighbors[b].add(a).add(c);
      neighbors[c].add(a).add(b);
    });
    const order = seeds.map((_, i) => i).sort(() => rand() - .5);
    const assigned = new Array(seeds.length).fill(false);
    order.forEach(a => {
      if (assigned[a]) return;
      const members = [a];
      assigned[a] = true;
      const grow = chance => {
        if (rand() > chance) return;
        const options = [];
        members.forEach(member => neighbors[member].forEach(nb => {
          if (!assigned[nb] && cellChain[nb][1] === cellChain[a][1]) options.push(nb);
        }));
        if (!options.length) return;
        const pick = options[Math.floor(rand() * options.length)];
        assigned[pick] = true;
        members.push(pick);
      };
      grow(.55);
      grow(.25);
      const fine = makeCluster(2, average(members.map(i => seeds[i])));
      fine.chain = cellChain[a];
      members.forEach(i => {
        cellChain[i][2] = fine;
      });
    });

    // 3) 조각 사이 경계선(edge): 어느 단계에서 갈라지는지 기록 (3 = 같은 조각이라 안 갈라짐)
    const edges = [];
    const edgeMap = new Map();
    const getEdge = (a, b) => {
      const key = a < b ? `${a},${b}` : `${b},${a}`;
      if (edgeMap.has(key)) return edgeMap.get(key);
      const shared = incident[a].filter(t => triangles[t].includes(b));
      const chainA = cellChain[a];
      const chainB = cellChain[b];
      const level = chainA[0] !== chainB[0] ? 0 : chainA[1] !== chainB[1] ? 1 : chainA[2] !== chainB[2] ? 2 : 3;
      const edge = {
        index: edges.length,
        chainA,
        chainB,
        level,
        mid: corners[shared[0]].clone().add(corners[shared[1]]).normalize()
      };
      edges.push(edge);
      edgeMap.set(key, edge);
      return edge;
    };
    const triEdges = new Int32Array(triangles.length * 3);
    triangles.forEach(([a, b, c], t) => {
      triEdges[t * 3] = getEdge(a, b).index;
      triEdges[t * 3 + 1] = getEdge(b, c).index;
      triEdges[t * 3 + 2] = getEdge(c, a).index;
    });

    // 4) 조각 형상: 윗면 + 둥근 모서리 + 옆벽 + 아랫면
    const dirs = [];
    const radii = [];
    const refKinds = [];
    const refs = [];
    const pieceOf = [];
    const kinds = [];
    const normalKinds = [];
    const normalBases = [];
    const index = [];
    const addVertex = (direction, radius, refKind, ref, piece, kind, normalKind = NORMAL_CAP, normalBase = direction) => {
      dirs.push(direction.x, direction.y, direction.z);
      radii.push(radius);
      refKinds.push(refKind);
      refs.push(ref);
      pieceOf.push(piece);
      kinds.push(kind);
      normalKinds.push(normalKind);
      normalBases.push(normalBase.x, normalBase.y, normalBase.z);
      return radii.length - 1;
    };
    const pa = new V();
    const pb = new V();
    const pc = new V();
    const addTri = (a, b, c, normal) => {
      pa.set(dirs[a * 3], dirs[a * 3 + 1], dirs[a * 3 + 2]).multiplyScalar(radii[a]);
      pb.set(dirs[b * 3], dirs[b * 3 + 1], dirs[b * 3 + 2]).multiplyScalar(radii[b]).sub(pa);
      pc.set(dirs[c * 3], dirs[c * 3 + 1], dirs[c * 3 + 2]).multiplyScalar(radii[c]).sub(pa);
      if (pb.cross(pc).dot(normal) < 0) index.push(a, c, b);
      else index.push(a, b, c);
    };
    const pieces = [];
    seeds.forEach((seed, a) => {
      // 각도 정렬 대신 삼각형 연결을 따라 한 바퀴 돌며 꼭짓점 순서를 정함
      // → 흔들림이 커도 이웃 조각과 경계가 항상 정확히 맞물림
      const ring = [];
      const ringNeighbors = [];
      let current = incident[a][0];
      for (let guard = 0; guard < incident[a].length; guard++) {
        const tri = triangles[current];
        const at = tri.indexOf(a);
        const following = tri[(at + 2) % 3];
        ring.push(current);
        ringNeighbors.push(following);
        current = incident[a].find(t => t !== current && triangles[t].includes(following));
        if (current === ring[0]) break;
      }
      const count = ring.length;
      const center = average(ring.map(t => corners[t]));
      const chain = cellChain[a];
      const piece = pieces.length;
      pieces.push({ chain, matrix: new THREE.Matrix4() });
      const segmentEdges = ringNeighbors.map(neighbor => getEdge(a, neighbor));
      const inset = direction => center.clone().lerp(direction, .84).normalize();
      const down = center.clone().negate();
      const outward = direction => direction.clone().sub(center).addScaledVector(direction, -direction.clone().sub(center).dot(direction)).normalize();

      const capCenter = addVertex(center, WAX_OUTER, 0, 0, piece, KIND_CAP);
      const insetCorner = ring.map(t => addVertex(inset(corners[t]), WAX_OUTER, 0, 0, piece, KIND_CAP));
      const bevelCorner = ring.map(t => addVertex(corners[t], WAX_OUTER, 1, t, piece, KIND_CAP, NORMAL_BEVEL, outward(corners[t])));
      const insetMid = segmentEdges.map(edge => addVertex(inset(edge.mid), WAX_OUTER, 0, 0, piece, KIND_CAP));
      const bevelMid = segmentEdges.map(edge => addVertex(edge.mid, WAX_OUTER, 2, edge.index, piece, KIND_CAP, NORMAL_BEVEL, outward(edge.mid)));
      const bottomCenter = addVertex(center, WAX_INNER, 0, 0, piece, KIND_WALL, NORMAL_BOTTOM);
      const bottomCorner = ring.map(t => addVertex(corners[t], WAX_INNER, 0, 0, piece, KIND_WALL, NORMAL_BOTTOM));
      const bottomMid = segmentEdges.map(edge => addVertex(edge.mid, WAX_INNER, 0, 0, piece, KIND_WALL, NORMAL_BOTTOM));

      for (let k = 0; k < count; k++) {
        const next = (k + 1) % count;
        const edge = segmentEdges[k];
        addTri(capCenter, insetCorner[k], insetMid[k], center);
        addTri(capCenter, insetMid[k], insetCorner[next], center);
        addTri(insetCorner[k], bevelCorner[k], bevelMid[k], center);
        addTri(insetCorner[k], bevelMid[k], insetMid[k], center);
        addTri(insetMid[k], bevelMid[k], bevelCorner[next], center);
        addTri(insetMid[k], bevelCorner[next], insetCorner[next], center);

        const wallNormal = edge.mid.clone().addScaledVector(center, -edge.mid.dot(center)).normalize();
        const c0 = corners[ring[k]];
        const c1 = corners[ring[next]];
        const top0 = addVertex(c0, WAX_OUTER, 1, ring[k], piece, KIND_WALL, NORMAL_WALL, wallNormal);
        const topMid = addVertex(edge.mid, WAX_OUTER, 2, edge.index, piece, KIND_WALL, NORMAL_WALL, wallNormal);
        const top1 = addVertex(c1, WAX_OUTER, 1, ring[next], piece, KIND_WALL, NORMAL_WALL, wallNormal);
        const low0 = addVertex(c0, WAX_INNER, 0, 0, piece, KIND_WALL, NORMAL_WALL, wallNormal);
        const lowMid = addVertex(edge.mid, WAX_INNER, 0, 0, piece, KIND_WALL, NORMAL_WALL, wallNormal);
        const low1 = addVertex(c1, WAX_INNER, 0, 0, piece, KIND_WALL, NORMAL_WALL, wallNormal);
        addTri(top0, low0, lowMid, wallNormal);
        addTri(top0, lowMid, topMid, wallNormal);
        addTri(topMid, lowMid, low1, wallNormal);
        addTri(topMid, low1, top1, wallNormal);

        addTri(bottomCenter, bottomCorner[k], bottomMid[k], down);
        addTri(bottomCenter, bottomMid[k], bottomCorner[next], down);
      }
    });

    const vertexCount = radii.length;
    const waxGeometry = new THREE.BufferGeometry();
    waxGeometry.setAttribute("position", new THREE.BufferAttribute(new Float32Array(vertexCount * 3), 3));
    waxGeometry.setAttribute("color", new THREE.BufferAttribute(new Float32Array(vertexCount * 3), 3));
    waxGeometry.setAttribute("normal", new THREE.BufferAttribute(new Float32Array(vertexCount * 3), 3));
    // 사진은 앞쪽에서 비추듯 입힘(가운데 기준으로 꽉 채움). 조각이 움직이면 사진도 같이 갈라짐
    const texture = getPhotoTexture();
    const uvs = new Float32Array(vertexCount * 2);
    const aspect = photoImage && photoImage.naturalWidth && photoImage.naturalHeight
      ? photoImage.naturalWidth / photoImage.naturalHeight
      : 1;
    const spanU = aspect > 1 ? 1 / aspect : 1;
    const spanV = aspect > 1 ? 1 : aspect;
    for (let v = 0; v < vertexCount; v++) {
      uvs[v * 2] = .5 + dirs[v * 3] * .5 * spanU;
      uvs[v * 2 + 1] = .5 + dirs[v * 3 + 1] * .5 * spanV;
    }
    waxGeometry.setAttribute("uv", new THREE.BufferAttribute(uvs, 2));
    waxGeometry.setIndex(index);
    const waxMaterial = new THREE.MeshPhysicalMaterial({
      color: "#ffffff",
      map: texture,
      vertexColors: true,
      roughness: .36,
      metalness: 0,
      clearcoat: .55,
      clearcoatRoughness: .32,
      side: THREE.DoubleSide
    });
    const waxMesh = new THREE.Mesh(waxGeometry, waxMaterial);
    waxMesh.frustumCulled = false;
    sphere.add(waxMesh);

    // 5) 점토 코어 (매끈한 측지 구, 정점 공유 → 부드러운 음영)
    const clay = geodesic(THREE, 22);
    const coreCount = clay.vertices.length;
    const coreDirs = new Float32Array(coreCount * 3);
    clay.vertices.forEach((vertex, i) => {
      coreDirs[i * 3] = vertex.x;
      coreDirs[i * 3 + 1] = vertex.y;
      coreDirs[i * 3 + 2] = vertex.z;
    });
    const coreGeometry = new THREE.BufferGeometry();
    coreGeometry.setAttribute("position", new THREE.BufferAttribute(new Float32Array(coreCount * 3), 3));
    coreGeometry.setAttribute("color", new THREE.BufferAttribute(new Float32Array(coreCount * 3), 3));
    coreGeometry.setIndex(clay.triangles.flat());
    const coreMaterial = new THREE.MeshPhysicalMaterial({
      color: "#ffffff",
      vertexColors: true,
      roughness: .86,
      metalness: 0,
      clearcoat: .05,
      clearcoatRoughness: .9
    });
    const coreMesh = new THREE.Mesh(coreGeometry, coreMaterial);
    coreMesh.frustumCulled = false;
    sphere.add(coreMesh);

    ball = {
      clusters,
      pieces,
      edges,
      triEdges,
      edgeProg: new Float32Array(edges.length),
      cornerProg: new Float32Array(triangles.length),
      waxGeometry,
      waxDirs: new Float32Array(dirs),
      waxRadii: new Float32Array(radii),
      waxRefKinds: new Uint8Array(refKinds),
      waxRefs: new Int32Array(refs),
      waxPieceOf: new Uint16Array(pieceOf),
      waxKinds: new Uint8Array(kinds),
      waxNormalKinds: new Uint8Array(normalKinds),
      waxNormalBases: new Float32Array(normalBases),
      waxDentTarget: new Float32Array(vertexCount),
      waxDentShown: new Float32Array(vertexCount),
      waxSlopeTarget: new Float32Array(vertexCount * 3),
      waxSlopeShown: new Float32Array(vertexCount * 3),
      fineClusters: clusters.filter(cluster => cluster.level === 2),
      coreGeometry,
      coreDirs,
      coreDentTarget: new Float32Array(coreCount),
      coreDentShown: new Float32Array(coreCount),
      coreMixTarget: new Float32Array(coreCount),
      coreMixShown: new Float32Array(coreCount),
      dentMoving: false,
      dirty: true,
      hold: { center: null, depth: 0, velocity: 0, target: 0, pressing: false, pressStart: 0, tick: 0 },
      tmpMatrix: new THREE.Matrix4(),
      pieceColors: new Float32Array(pieces.length * 3),
      photo: !!texture,
      separated: 0
    };
    raycaster = new THREE.Raycaster();
    refreshBall();
  }

  // 단계별 갈라짐: 큰 금 → 중간 금 → 낱조각 → 점토에 박힘
  function updateClusterMatrix(cluster, tmp) {
    const damage = cluster.shown;
    let scale;
    let sink;
    let tilt;
    let drift = 0;
    if (cluster.level === 0) {
      const p = smooth(damage, .1, .9);
      cluster.p = p;
      scale = 1 - .028 * p;
      sink = .002 * p;
      tilt = .03 * p * cluster.tilt;
    } else if (cluster.level === 1) {
      const p = smooth(damage, .8, 1.9);
      cluster.p = p;
      scale = 1 - .045 * p;
      sink = .003 * p;
      tilt = .06 * p * cluster.tilt;
    } else {
      const p = smooth(damage, 1.6, 2.9);
      const q = smooth(damage, 2.8, 5.6);
      cluster.p = p;
      cluster.q = q;
      scale = 1 - .07 * p - .1 * q * cluster.shrink;
      sink = .004 * p + .016 * q;
      tilt = (.05 * p + .3 * q) * cluster.tilt;
      drift = .014 * q;
    }
    const c = cluster.center;
    const pivot = .978;
    const matrix = cluster.matrix;
    const push = cluster.push;
    if (scale === 1 && sink === 0 && tilt === 0 && drift === 0 && push.lengthSq() === 0) {
      // 아직 안 갈라진 곳은 정확히 단위 행렬 → 이웃 조각과 이음새가 안 보임
      matrix.identity();
      return;
    }
    matrix.makeTranslation(-c.x * pivot, -c.y * pivot, -c.z * pivot);
    tmp.makeScale(scale, scale, scale);
    matrix.premultiply(tmp);
    if (tilt) {
      tmp.makeRotationAxis(cluster.axis, tilt);
      matrix.premultiply(tmp);
    }
    tmp.makeTranslation(
      c.x * (pivot - sink) + cluster.drift.x * drift + push.x,
      c.y * (pivot - sink) + cluster.drift.y * drift + push.y,
      c.z * (pivot - sink) + cluster.drift.z * drift + push.z
    );
    matrix.premultiply(tmp);
  }

  function refreshBall() {
    const b = ball;
    if (!b) return;
    b.clusters.forEach(cluster => updateClusterMatrix(cluster, b.tmpMatrix));
    b.edges.forEach(edge => {
      b.edgeProg[edge.index] = edge.level > 2
        ? 0
        : (edge.chainA[edge.level].p + edge.chainB[edge.level].p) * .5;
    });
    for (let t = 0; t < b.cornerProg.length; t++) {
      b.cornerProg[t] = Math.max(
        b.edgeProg[b.triEdges[t * 3]],
        b.edgeProg[b.triEdges[t * 3 + 1]],
        b.edgeProg[b.triEdges[t * 3 + 2]]
      );
    }
    // 기본은 진한 왁스 빨강(#c0281f 근처), 사진이 있으면 사진 색 그대로
    const base = b.photo ? [1, 1, 1] : [.5, .03, .024];
    b.pieces.forEach((piece, i) => {
      piece.matrix.multiplyMatrices(piece.chain[0].matrix, piece.chain[1].matrix).multiply(piece.chain[2].matrix);
      const fine = piece.chain[2];
      const variation = 1 + fine.tint * (.04 * piece.chain[0].p + .08 * fine.p);
      const darken = 1 - .12 * fine.q;
      b.pieceColors[i * 3] = base[0] * variation * darken;
      b.pieceColors[i * 3 + 1] = base[1] * variation * darken;
      b.pieceColors[i * 3 + 2] = base[2] * variation * darken;
    });

    const hold = b.hold;
    const holdActive = hold.center && Math.abs(hold.depth) > 1e-4;
    const hx = holdActive ? hold.center.x : 0;
    const hy = holdActive ? hold.center.y : 0;
    const hz = holdActive ? hold.center.z : 0;

    const positions = b.waxGeometry.getAttribute("position");
    const colors = b.waxGeometry.getAttribute("color");
    const normals = b.waxGeometry.getAttribute("normal");
    const pos = positions.array;
    const col = colors.array;
    const nor = normals.array;
    const dirs = b.waxDirs;
    const bases = b.waxNormalBases;
    const slope = b.waxSlopeShown;
    const holdSlope = [0, 0, 0];
    for (let v = 0; v < b.waxRadii.length; v++) {
      const piece = b.waxPieceOf[v];
      const e = b.pieces[piece].matrix.elements;
      const refKind = b.waxRefKinds[v];
      let radius = b.waxRadii[v];
      let prog = 0;
      if (refKind === 1) prog = b.cornerProg[b.waxRefs[v]];
      else if (refKind === 2) prog = b.edgeProg[b.waxRefs[v]];
      radius -= BEVEL_DROP * prog;
      // 안 갈라진 곳은 옆벽 높이를 0으로 접어 둠 → 이음새가 비쳐 보이지 않음
      if (refKind && b.waxKinds[v] === KIND_WALL) {
        radius = WAX_INNER + (radius - WAX_INNER) * Math.min(1, prog * 4);
      }
      const i3 = v * 3;
      const dx = dirs[i3];
      const dy = dirs[i3 + 1];
      const dz = dirs[i3 + 2];
      const x = dx * radius;
      const y = dy * radius;
      const z = dz * radius;
      let dent = b.waxDentShown[v];
      if (holdActive) dent += hold.depth * dentShape(dx * hx + dy * hy + dz * hz);
      const k = 1 - dent;
      pos[i3] = (e[0] * x + e[4] * y + e[8] * z + e[12]) * k;
      pos[i3 + 1] = (e[1] * x + e[5] * y + e[9] * z + e[13]) * k;
      pos[i3 + 2] = (e[2] * x + e[6] * y + e[10] * z + e[14]) * k;

      // 법선: 조각 자체 기울기 + 둥근 모서리 + 점토 자국 기울기
      const normalKind = b.waxNormalKinds[v];
      let nx;
      let ny;
      let nz;
      if (normalKind === NORMAL_CAP) {
        nx = dx; ny = dy; nz = dz;
      } else if (normalKind === NORMAL_BEVEL) {
        const blend = .75 * prog;
        nx = dx * (1 - blend) + bases[i3] * blend;
        ny = dy * (1 - blend) + bases[i3 + 1] * blend;
        nz = dz * (1 - blend) + bases[i3 + 2] * blend;
      } else if (normalKind === NORMAL_WALL) {
        nx = bases[i3]; ny = bases[i3 + 1]; nz = bases[i3 + 2];
      } else {
        nx = -dx; ny = -dy; nz = -dz;
      }
      let rx = e[0] * nx + e[4] * ny + e[8] * nz;
      let ry = e[1] * nx + e[5] * ny + e[9] * nz;
      let rz = e[2] * nx + e[6] * ny + e[10] * nz;
      if (normalKind <= NORMAL_BEVEL) {
        rx += slope[i3];
        ry += slope[i3 + 1];
        rz += slope[i3 + 2];
        if (holdActive) {
          holdSlope[0] = holdSlope[1] = holdSlope[2] = 0;
          addDentSlope(holdSlope, 0, dx, dy, dz, hx, hy, hz, hold.depth);
          rx += holdSlope[0];
          ry += holdSlope[1];
          rz += holdSlope[2];
        }
      }
      const length = Math.hypot(rx, ry, rz) || 1;
      nor[i3] = rx / length;
      nor[i3 + 1] = ry / length;
      nor[i3 + 2] = rz / length;

      const shade = b.waxKinds[v] === KIND_WALL ? .72 : 1;
      col[i3] = b.pieceColors[piece * 3] * shade;
      col[i3 + 1] = b.pieceColors[piece * 3 + 1] * shade;
      col[i3 + 2] = b.pieceColors[piece * 3 + 2] * shade;
    }
    positions.needsUpdate = true;
    colors.needsUpdate = true;
    normals.needsUpdate = true;

    const corePositions = b.coreGeometry.getAttribute("position");
    const coreColors = b.coreGeometry.getAttribute("color");
    const cpos = corePositions.array;
    const ccol = coreColors.array;
    const cdirs = b.coreDirs;
    for (let v = 0; v < b.coreDentShown.length; v++) {
      const i3 = v * 3;
      const dx = cdirs[i3];
      const dy = cdirs[i3 + 1];
      const dz = cdirs[i3 + 2];
      let dent = b.coreDentShown[v];
      if (holdActive) dent += hold.depth * dentShape(dx * hx + dy * hy + dz * hz);
      const radius = CLAY_RADIUS * (1 - dent);
      cpos[i3] = dx * radius;
      cpos[i3 + 1] = dy * radius;
      cpos[i3 + 2] = dz * radius;
      // 왁스가 섞일수록 점토에 붉은 기
      const mix = Math.min(.42, b.coreMixShown[v]);
      ccol[i3] = .9 + (.74 - .9) * mix;
      ccol[i3 + 1] = .86 + (.3 - .86) * mix;
      ccol[i3 + 2] = .79 + (.27 - .79) * mix;
    }
    corePositions.needsUpdate = true;
    coreColors.needsUpdate = true;
    b.coreGeometry.computeVertexNormals();
    b.dirty = false;
  }

  // 매 프레임: 갈라짐/눌림을 부드럽게 따라가게 함
  function stepBall(dt) {
    const b = ball;
    if (!b || dt <= 0) return b ? b.dirty : false;
    let changed = b.dirty;

    const hold = b.hold;
    if (hold.pressing) {
      // 오래 누를수록 더 깊이 들어가고, 0.3초마다 조금씩 더 갈라져 파묻힘
      const heldFor = (performance.now() - hold.pressStart) / 1000;
      hold.target = .06 + Math.min(.12, heldFor * .08);
      hold.tick += dt;
      if (hold.tick >= .3) {
        hold.tick = 0;
        pressSphere(hold.center, .28, true);
      }
    }
    const stiffness = 240;
    const damping = 2 * Math.sqrt(stiffness) * .75;
    const acceleration = (hold.target - hold.depth) * stiffness - hold.velocity * damping;
    hold.velocity += acceleration * dt;
    hold.depth += hold.velocity * dt;
    if (Math.abs(hold.velocity) > 1e-4 || Math.abs(hold.target - hold.depth) > 1e-4) {
      changed = true;
    } else if (hold.depth !== hold.target) {
      hold.depth = hold.target;
      hold.velocity = 0;
      changed = true;
    }

    const crackRate = 1 - Math.exp(-dt * 13);
    b.clusters.forEach(cluster => {
      const diff = cluster.damage - cluster.shown;
      if (diff > 1e-3) {
        cluster.shown += diff * crackRate;
        changed = true;
      } else if (diff !== 0) {
        cluster.shown = cluster.damage;
        changed = true;
      }
    });

    if (b.dentMoving) {
      const rate = 1 - Math.exp(-dt * 7);
      let maxDiff = 0;
      const follow = (target, shown) => {
        for (let i = 0; i < target.length; i++) {
          const diff = target[i] - shown[i];
          shown[i] += diff * rate;
          if (Math.abs(diff) > maxDiff) maxDiff = Math.abs(diff);
        }
      };
      follow(b.waxDentTarget, b.waxDentShown);
      follow(b.waxSlopeTarget, b.waxSlopeShown);
      follow(b.coreDentTarget, b.coreDentShown);
      follow(b.coreMixTarget, b.coreMixShown);
      if (maxDiff < 2e-4) {
        b.waxDentShown.set(b.waxDentTarget);
        b.waxSlopeShown.set(b.waxSlopeTarget);
        b.coreDentShown.set(b.coreDentTarget);
        b.coreMixShown.set(b.coreMixTarget);
        b.dentMoving = false;
      }
      changed = true;
    }
    return changed;
  }

  function getAudioContext() {
    const AudioContext = window.AudioContext || window.webkitAudioContext;
    if (!AudioContext) return null;
    if (!audioContext) audioContext = new AudioContext();
    if (audioContext.state === "suspended") {
      audioContext.resume().catch(error => console.warn("오디오를 시작하지 못했어요.", error));
    }
    if (!audioNoiseBuffer) {
      const sampleCount = Math.floor(audioContext.sampleRate * .16);
      audioNoiseBuffer = audioContext.createBuffer(1, sampleCount, audioContext.sampleRate);
      const samples = audioNoiseBuffer.getChannelData(0);
      for (let index = 0; index < sampleCount; index++) {
        samples[index] = Math.random() * 2 - 1;
      }
    }
    return audioContext;
  }

  function playBubbleSound() {
    const context = getAudioContext();
    if (!context) return;
    const now = context.currentTime;
    const pop = context.createBufferSource();
    const filter = context.createBiquadFilter();
    const gain = context.createGain();
    pop.buffer = audioNoiseBuffer;
    pop.playbackRate.value = .8 + Math.random() * .5;
    filter.type = "bandpass";
    filter.frequency.value = 1500 + Math.random() * 1700;
    filter.Q.value = 1.2 + Math.random() * .8;
    gain.gain.setValueAtTime(.0001, now);
    gain.gain.exponentialRampToValueAtTime(.08 + Math.random() * .035, now + .003);
    gain.gain.exponentialRampToValueAtTime(.0001, now + .065);
    pop.connect(filter);
    filter.connect(gain);
    gain.connect(context.destination);
    pop.start(now, Math.random() * .08);
    pop.stop(now + .07);
  }

  function playWaxSound(waxRatio, crackCount = 0) {
    const context = getAudioContext();
    if (!context) return;
    const now = audioContext.currentTime;
    const duration = .1 + Math.random() * .035;
    const noise = audioContext.createBufferSource();
    const filter = audioContext.createBiquadFilter();
    const noiseGain = audioContext.createGain();
    noise.buffer = audioNoiseBuffer;
    filter.type = "bandpass";
    filter.frequency.value = 850 + waxRatio * (700 + Math.random() * 700);
    filter.Q.value = .8 + Math.random() * .5;
    noiseGain.gain.setValueAtTime(.0001, now);
    noiseGain.gain.exponentialRampToValueAtTime(.026 + waxRatio * .035, now + .006);
    noiseGain.gain.exponentialRampToValueAtTime(.0001, now + duration);
    noise.connect(filter);
    filter.connect(noiseGain);
    noiseGain.connect(audioContext.destination);
    noise.start(now);
    noise.stop(now + duration);

    // 새로 갈라진 곳이 많을수록 자잘한 '바삭' 소리를 더 냄
    const burstCount = 2 + Math.min(7, Math.round(crackCount / 5));
    for (let index = 0; index < burstCount; index++) {
      const burstDuration = .014 + Math.random() * .018;
      const burst = audioContext.createBufferSource();
      const burstFilter = audioContext.createBiquadFilter();
      const burstGain = audioContext.createGain();
      burst.buffer = audioNoiseBuffer;
      burstFilter.type = "bandpass";
      burstFilter.frequency.value = 1350 + Math.random() * 1250;
      burstFilter.Q.value = .75 + Math.random() * .45;
      burst.connect(burstFilter);
      burstFilter.connect(burstGain);
      burstGain.connect(audioContext.destination);
      const startAt = now + index * (.011 + Math.random() * .012);
      burstGain.gain.setValueAtTime(.0001, startAt);
      burstGain.gain.exponentialRampToValueAtTime(.009 + waxRatio * .014, startAt + .002);
      burstGain.gain.exponentialRampToValueAtTime(.0001, startAt + burstDuration);
      burst.start(startAt);
      burst.stop(startAt + burstDuration);
    }

    const wet = audioContext.createBufferSource();
    const wetFilter = audioContext.createBiquadFilter();
    const wetGain = audioContext.createGain();
    wet.buffer = audioNoiseBuffer;
    wetFilter.type = "lowpass";
    wetFilter.frequency.setValueAtTime(420 + (1 - waxRatio) * 260, now);
    wetFilter.frequency.exponentialRampToValueAtTime(180, now + .16);
    wetGain.gain.setValueAtTime(.0001, now);
    wetGain.gain.exponentialRampToValueAtTime(.018 + (1 - waxRatio) * .025, now + .025);
    wetGain.gain.exponentialRampToValueAtTime(.0001, now + .17);
    wet.connect(wetFilter);
    wetFilter.connect(wetGain);
    wetGain.connect(audioContext.destination);
    wet.start(now);
    wet.stop(now + .18);

    const suction = audioContext.createOscillator();
    const suctionGain = audioContext.createGain();
    suction.type = "sine";
    suction.frequency.setValueAtTime(155 - waxRatio * 35, now);
    suction.frequency.exponentialRampToValueAtTime(92, now + .12);
    suctionGain.gain.setValueAtTime(.0001, now);
    suctionGain.gain.exponentialRampToValueAtTime(.009 + (1 - waxRatio) * .008, now + .018);
    suctionGain.gain.exponentialRampToValueAtTime(.0001, now + .13);
    suction.connect(suctionGain);
    suctionGain.connect(audioContext.destination);
    suction.start(now);
    suction.stop(now + .14);
  }

  // 지금 눌려 있는 모양을 굳혀서 다시 올라오지 않게 함
  // fraction < 1 이면 일부만 굳힘 (문지를 때 지나간 자리에 자국을 남기는 용도)
  function commitHold(fraction = 1) {
    const b = ball;
    if (!b) return;
    const hold = b.hold;
    if (hold.center && Math.abs(hold.depth) > 1e-4) {
      const c = hold.center;
      const depth = hold.depth * fraction;
      for (let v = 0; v < b.waxDentTarget.length; v++) {
        const i3 = v * 3;
        const ux = b.waxDirs[i3];
        const uy = b.waxDirs[i3 + 1];
        const uz = b.waxDirs[i3 + 2];
        const weight = dentShape(ux * c.x + uy * c.y + uz * c.z);
        if (weight === 0) continue;
        const previous = b.waxDentTarget[v];
        const next = Math.min(.3, Math.max(-.05, previous + depth * weight));
        const added = next - previous;
        b.waxDentTarget[v] = next;
        b.waxDentShown[v] += added;
        const applied = Math.abs(weight) > 1e-6 ? added / weight : 0;
        addDentSlope(b.waxSlopeTarget, i3, ux, uy, uz, c.x, c.y, c.z, applied);
        addDentSlope(b.waxSlopeShown, i3, ux, uy, uz, c.x, c.y, c.z, applied);
      }
      for (let v = 0; v < b.coreDentTarget.length; v++) {
        const i3 = v * 3;
        const weight = dentShape(b.coreDirs[i3] * c.x + b.coreDirs[i3 + 1] * c.y + b.coreDirs[i3 + 2] * c.z);
        if (weight === 0) continue;
        const previous = b.coreDentTarget[v];
        const next = Math.min(.3, Math.max(-.05, previous + depth * weight));
        b.coreDentTarget[v] = next;
        b.coreDentShown[v] += next - previous;
      }
      b.dentMoving = true;
    }
    if (fraction >= 1) {
      hold.depth = 0;
      hold.velocity = 0;
      hold.target = 0;
      hold.pressing = false;
    } else {
      hold.depth *= 1 - fraction;
    }
    b.dirty = true;
  }

  // 문지른 방향으로 손가락 아래 조각들을 밀어서 옆으로 퍼지게 함
  function pushPieces(from, to) {
    const b = ball;
    if (!b) return;
    const move = to.clone().sub(from);
    const tangent = new window.THREE.Vector3();
    b.fineClusters.forEach(fine => {
      const dot = fine.center.dot(to);
      if (dot < .92) return;
      const angle = Math.acos(Math.min(1, dot));
      const weight = Math.exp(-angle * angle / .028);
      tangent.copy(move).addScaledVector(fine.center, -move.dot(fine.center));
      fine.push.addScaledVector(tangent, weight * .85);
      if (fine.push.length() > .14) fine.push.setLength(.14);
    });
    b.dirty = true;
  }

  function addDent(dirs, target, center, depth, min, max) {
    for (let i = 0; i < target.length; i++) {
      const i3 = i * 3;
      const weight = dentShape(dirs[i3] * center.x + dirs[i3 + 1] * center.y + dirs[i3 + 2] * center.z);
      if (weight === 0) continue;
      target[i] = Math.min(max, Math.max(min, target[i] + depth * weight));
    }
  }

  function spherePointAt(clientX, clientY) {
    if (!renderer || !sphere || !raycaster) return null;
    const THREE = window.THREE;
    const bounds = canvas.getBoundingClientRect();
    const ndc = new THREE.Vector2(
      ((clientX - bounds.left) / bounds.width) * 2 - 1,
      -((clientY - bounds.top) / bounds.height) * 2 + 1
    );
    raycaster.setFromCamera(ndc, camera);
    sphere.updateMatrixWorld(true);
    const ray = raycaster.ray.clone().applyMatrix4(sphere.matrixWorld.clone().invert());
    const hit = ray.intersectSphere(new THREE.Sphere(new THREE.Vector3(), 1), new THREE.Vector3());
    return hit ? hit.normalize() : null;
  }

  function pieceStage(fine) {
    const [coarse, medium] = fine.chain;
    return (coarse.damage > .1) + (medium.damage > .8) + (fine.damage > 1.6) + (fine.damage > 2.8);
  }

  let lastSoftSoundAt = 0;

  // quiet: 꾹 누르고 있거나 문지르는 중의 작은 갈라짐 (소리는 가끔, 작게)
  function pressSphere(center, amount, quiet = false) {
    const b = ball;
    if (!b || !center) return;
    const before = b.fineClusters.map(pieceStage);

    let waxWeight = 0;
    let pressWeight = 0;
    b.fineClusters.forEach(fine => {
      const dot = fine.center.dot(center);
      if (dot < .8) return;
      const weight = Math.exp(-(1 - dot) * 12);
      waxWeight += weight * Math.exp(-fine.damage * .3);
      pressWeight += weight;
    });
    const waxRatio = pressWeight ? waxWeight / pressWeight : 0;

    b.clusters.forEach(cluster => {
      const dot = cluster.center.dot(center);
      if (dot < .35) return;
      const angle = Math.acos(Math.min(1, dot));
      // 누른 자리는 한 번에 낱조각까지 확 갈라지고, 주변으로 갈수록 큰 금만 퍼짐
      const burst = 3.3 * Math.exp(-angle * angle / .05) + (quiet ? .35 : .95) * Math.exp(-angle * angle / .22);
      cluster.damage += amount * burst * (.85 + Math.random() * .3);
    });

    let newCracks = 0;
    b.fineClusters.forEach((fine, i) => {
      newCracks += pieceStage(fine) - before[i];
    });
    const separated = b.fineClusters.filter(fine => fine.damage > 1.6).length;
    b.separated = separated;
    b.dirty = true;

    if (quiet) {
      addDent(b.coreDirs, b.coreMixTarget, center, .09 * amount, 0, 1);
      b.dentMoving = true;
      const now = performance.now();
      if (newCracks > 0 && now - lastSoftSoundAt > 110) {
        lastSoftSoundAt = now;
        playWaxSound(waxRatio * .5, newCracks);
        if (typeof window.navigator.vibrate === "function") window.navigator.vibrate(6);
      }
      if (newCracks) status.textContent = `왁스가 밀리며 갈라져요 · 떨어진 조각 ${separated}개`;
      return;
    }

    const dentDepth = .015 * amount;
    for (let v = 0; v < b.waxDentTarget.length; v++) {
      const previous = b.waxDentTarget[v];
      const i3 = v * 3;
      const ux = b.waxDirs[i3];
      const uy = b.waxDirs[i3 + 1];
      const uz = b.waxDirs[i3 + 2];
      const weight = dentShape(ux * center.x + uy * center.y + uz * center.z);
      if (weight === 0) continue;
      const next = Math.min(.3, Math.max(-.05, previous + dentDepth * weight));
      b.waxDentTarget[v] = next;
      // 자국이 한계에 닿아 더 안 깊어지면 기울기도 그만큼만 더함
      const applied = Math.abs(weight) > 1e-6 ? (next - previous) / weight : 0;
      addDentSlope(b.waxSlopeTarget, i3, ux, uy, uz, center.x, center.y, center.z, applied);
    }
    addDent(b.coreDirs, b.coreDentTarget, center, .015 * amount, -.05, .3);
    addDent(b.coreDirs, b.coreMixTarget, center, .09 * amount, 0, 1);
    b.dentMoving = true;

    playWaxSound(waxRatio, newCracks);
    if (typeof window.navigator.vibrate === "function") {
      window.navigator.vibrate(Math.round(10 + waxRatio * 30 + Math.min(20, newCracks)));
    }
    status.textContent = newCracks
      ? `왁스가 ${newCracks}군데 더 갈라졌어요 · 떨어진 조각 ${separated}개`
      : `말랑하게 눌렸어요 · 떨어진 조각 ${separated}개`;
  }

  function renderFrame(timestamp = 0) {
    if (!renderer || !sphere) return;
    rotationFrame = requestAnimationFrame(renderFrame);
    const delta = previousFrame ? Math.min(.05, (timestamp - previousFrame) / 1000) : 0;
    previousFrame = timestamp;
    if (!pointer) {
      sphere.rotation.y += velocityX * delta * 60;
      sphere.rotation.x = Math.max(-1.35, Math.min(1.35, sphere.rotation.x + velocityY * delta * 60));
      velocityX *= Math.pow(.94, delta * 60);
      velocityY *= Math.pow(.94, delta * 60);
    }
    if (stepBall(delta)) refreshBall();
    renderer.render(scene, camera);
  }

  function resizeSphere() {
    if (!renderer || !camera) return;
    const bounds = wrapper.getBoundingClientRect();
    const width = Math.max(1, Math.floor(bounds.width));
    const height = Math.max(1, Math.floor(bounds.height));
    renderer.setSize(width, height, false);
    renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 1.5));
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
  }

  function disposeSphereContents() {
    if (!sphere) return;
    sphere.children.forEach(child => {
      child.geometry?.dispose();
      if (Array.isArray(child.material)) child.material.forEach(material => material.dispose());
      else child.material?.dispose();
    });
    scene.remove(sphere);
    sphere = null;
    ball = null;
  }

  function startSphere() {
    if (!window.THREE) {
      status.textContent = "3D 구체를 불러오지 못했어요. 인터넷 연결을 확인해 주세요.";
      return;
    }
    chooseScreen.hidden = true;
    bubbleScreen.hidden = true;
    sphereScreen.hidden = false;
    status.textContent = "";
    if (renderer) {
      resizeSphere();
      if (!sphere) {
        sphere = new window.THREE.Group();
        if (!photoImage) sphere.rotation.set(.35, -.4, 0);
        scene.add(sphere);
        buildSphere();
        velocityX = 0;
        velocityY = 0;
        previousFrame = 0;
        renderFrame();
      }
      return;
    }

    const THREE = window.THREE;
    try {
      renderer = new THREE.WebGLRenderer({ canvas, alpha: true, antialias: true, powerPreference: "low-power" });
      renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 1.5));
      renderer.outputColorSpace = THREE.SRGBColorSpace;
      renderer.toneMapping = THREE.NoToneMapping;
      scene = new THREE.Scene();
      // near/far를 구체에 딱 맞춰 깊이 정밀도를 높임 (이음새 깜빡임 방지)
      camera = new THREE.PerspectiveCamera(34, 1, 2.6, 5.6);
      camera.position.set(0, 0, 4.1);
      scene.add(new THREE.HemisphereLight(0xfffaf4, 0x8a6a6a, .72));
      const keyLight = new THREE.DirectionalLight(0xffffff, .78);
      keyLight.position.set(-3, 4, 5);
      scene.add(keyLight);
      const fillLight = new THREE.DirectionalLight(0xffd6cc, .16);
      fillLight.position.set(3, -1, 3);
      scene.add(fillLight);
      sphere = new THREE.Group();
      // 사진이 있으면 사진이 정면으로 보이게 시작
      if (!photoImage) sphere.rotation.set(.35, -.4, 0);
      scene.add(sphere);
      buildSphere();
      resizeSphere();
      velocityX = 0;
      velocityY = 0;
      previousFrame = 0;
      renderFrame();
    } catch (error) {
      console.error("왁뿌볼 3D 구체 생성 실패", error);
      renderer?.dispose();
      renderer = null;
      status.textContent = "이 기기에서 3D 구체를 만들지 못했어요.";
    }
  }

  function pointerDown(event) {
    if (!renderer || !event.isPrimary) return;
    event.preventDefault();
    canvas.setPointerCapture(event.pointerId);
    pointer = {
      rotate: rotateMode,
      lastX: event.clientX,
      lastY: event.clientY,
      center: rotateMode ? null : spherePointAt(event.clientX, event.clientY)
    };
    velocityX = 0;
    velocityY = 0;
    if (pointer.center && ball) {
      // 누르는 순간 바로 확 갈라지고, 누르고 있는 동안 점토가 계속 들어감
      const hold = ball.hold;
      hold.center = pointer.center;
      hold.pressing = true;
      hold.pressStart = performance.now();
      hold.tick = 0;
      hold.target = .06;
      pressSphere(pointer.center, 1);
    }
  }

  function pointerMove(event) {
    if (!pointer || !sphere) return;
    const deltaX = event.clientX - pointer.lastX;
    const deltaY = event.clientY - pointer.lastY;
    pointer.lastX = event.clientX;
    pointer.lastY = event.clientY;
    if (pointer.rotate) {
      const sensitivity = .008;
      sphere.rotation.y += deltaX * sensitivity;
      sphere.rotation.x = Math.max(-1.35, Math.min(1.35, sphere.rotation.x + deltaY * sensitivity));
      velocityX = deltaX * sensitivity;
      velocityY = deltaY * sensitivity;
      return;
    }
    if (!pointer.center || !ball) return;
    const next = spherePointAt(event.clientX, event.clientY);
    if (!next) return;
    const moved = Math.acos(Math.min(1, pointer.center.dot(next)));
    if (moved < .006) return;
    // 문지르기: 지나간 자리에 자국을 남기고, 조각을 그 방향으로 밀고, 점토가 손가락을 따라감
    commitHold(Math.min(.5, moved * 6));
    pushPieces(pointer.center, next);
    pointer.center = next;
    ball.hold.center = next;
    pressSphere(next, Math.min(.6, moved * 4), true);
  }

  function pointerUp() {
    if (pointer && !pointer.rotate && pointer.center && ball) {
      // 눌린 자리는 다시 올라오지 않음
      commitHold();
    }
    pointer = null;
  }

  function setRotateMode(on) {
    rotateMode = on;
    const button = $("#rotate-toggle");
    button.setAttribute("aria-pressed", on ? "true" : "false");
    button.classList.toggle("active", on);
    canvas.classList.toggle("rotate-mode", on);
    $("#sphere-hint-text").textContent = on
      ? "드래그해서 돌려보기 · 버튼을 끄면 다시 눌러요"
      : "꾹 누르고 문질러 보세요 · 돌리려면 ↻ 버튼";
  }

  function updateBubbleCounter() {
    bubbleCounter.textContent = poppedBubbleCount === totalBubbleCount
      ? `모두 터뜨렸어요! ${poppedBubbleCount}개`
      : `${poppedBubbleCount}개 터뜨렸어요`;
  }

  function buildBubbleSheet(reset = false) {
    const previousPopped = reset ? 0 : poppedBubbleCount;
    const columns = Math.max(5, Math.ceil(window.innerWidth / 60));
    const rows = Math.max(6, Math.ceil((window.innerHeight - 148) / 58));
    totalBubbleCount = columns * rows;
    poppedBubbleCount = Math.min(previousPopped, totalBubbleCount);
    bubbleGrid.replaceChildren();
    bubbleGrid.style.setProperty("--columns", columns);
    for (let index = 0; index < totalBubbleCount; index++) {
      const bubble = document.createElement("button");
      bubble.type = "button";
      bubble.className = "air-bubble";
      bubble.setAttribute("aria-label", `${index + 1}번 기포 터뜨리기`);
      bubble.setAttribute("aria-pressed", index < poppedBubbleCount ? "true" : "false");
      if (index < poppedBubbleCount) {
        bubble.classList.add("popped");
        bubble.disabled = true;
      } else {
        bubble.addEventListener("click", () => {
          if (bubble.disabled) return;
          bubble.classList.add("popped");
          bubble.setAttribute("aria-pressed", "true");
          bubble.disabled = true;
          poppedBubbleCount++;
          updateBubbleCounter();
          playBubbleSound();
          if (typeof window.navigator.vibrate === "function") {
            window.navigator.vibrate(9);
          }
        });
      }
      bubbleGrid.append(bubble);
    }
    updateBubbleCounter();
  }

  function startBubbles() {
    chooseScreen.hidden = true;
    sphereScreen.hidden = true;
    bubbleScreen.hidden = false;
    buildBubbleSheet(true);
  }

  function backToChooseFromBubbles() {
    bubbleScreen.hidden = true;
    chooseScreen.hidden = false;
  }

  function backToChoose() {
    cancelAnimationFrame(rotationFrame);
    rotationFrame = 0;
    disposeSphereContents();
    velocityX = 0;
    velocityY = 0;
    previousFrame = 0;
    sphereScreen.hidden = true;
    bubbleScreen.hidden = true;
    chooseScreen.hidden = false;
    pointer = null;
  }

  // ── 내 사진 넣기 ────────────────────────────────────────────
  function getPhotoTexture() {
    const THREE = window.THREE;
    if (!photoImage || !THREE) return null;
    if (!photoTexture) {
      photoTexture = new THREE.Texture(photoImage);
      photoTexture.colorSpace = THREE.SRGBColorSpace;
      photoTexture.anisotropy = 4;
      if (photoImage.complete && photoImage.naturalWidth) photoTexture.needsUpdate = true;
    }
    return photoTexture;
  }

  function updatePhotoUI() {
    const thumb = $("#photo-thumb");
    const preview = $(".wax-preview");
    const has = !!photoDataUrl;
    const css = has ? `url("${photoDataUrl}")` : "";
    thumb.style.backgroundImage = css;
    thumb.classList.toggle("has-photo", has);
    preview.style.backgroundImage = css;
    preview.classList.toggle("has-photo", has);
    bubbleScreen.style.backgroundImage = css;
    bubbleScreen.classList.toggle("has-photo", has);
    $("#photo-clear").hidden = !has;
    $("#photo-status").textContent = has
      ? "왁뿌볼과 뽁뽁이에 내 사진이 입혀져요"
      : "사진을 넣으면 왁뿌볼과 뽁뽁이에 입혀져요";
  }

  function setPhoto(dataUrl, save) {
    photoDataUrl = dataUrl;
    photoTexture?.dispose();
    photoTexture = null;
    photoImage = null;
    if (dataUrl) {
      const image = new Image();
      image.onload = () => {
        if (photoTexture && photoTexture.image === image) photoTexture.needsUpdate = true;
      };
      image.src = dataUrl;
      photoImage = image;
    }
    if (save) {
      try {
        if (dataUrl) localStorage.setItem(PHOTO_KEY, dataUrl);
        else localStorage.removeItem(PHOTO_KEY);
      } catch (error) {
        console.warn("사진을 브라우저에 저장하지 못했어요. 이번에만 사용돼요.", error);
      }
    }
    updatePhotoUI();
  }

  function loadPhotoFile(file) {
    if (!file || !file.type.startsWith("image/")) return;
    const url = URL.createObjectURL(file);
    const image = new Image();
    image.onload = () => {
      // 너무 큰 사진은 줄여서 저장(최대 1280px)
      const scale = Math.min(1, 1280 / Math.max(image.naturalWidth, image.naturalHeight));
      const width = Math.max(1, Math.round(image.naturalWidth * scale));
      const height = Math.max(1, Math.round(image.naturalHeight * scale));
      const resized = document.createElement("canvas");
      resized.width = width;
      resized.height = height;
      resized.getContext("2d").drawImage(image, 0, 0, width, height);
      URL.revokeObjectURL(url);
      setPhoto(resized.toDataURL("image/jpeg", .86), true);
    };
    image.onerror = () => {
      URL.revokeObjectURL(url);
      $("#photo-status").textContent = "이 사진은 열 수 없어요. 다른 사진을 골라 주세요.";
    };
    image.src = url;
  }

  $("#photo-input").addEventListener("change", event => {
    loadPhotoFile(event.target.files[0]);
    event.target.value = "";
  });
  $("#photo-clear").addEventListener("click", () => setPhoto(null, true));
  try {
    const saved = localStorage.getItem(PHOTO_KEY);
    if (saved) setPhoto(saved, false);
  } catch (error) {
    // 저장소를 못 쓰는 환경이면 사진 없이 시작
  }

  $("#start-bubble").addEventListener("click", startBubbles);
  $("#bubble-back-button").addEventListener("click", backToChooseFromBubbles);
  $("#start-wax").addEventListener("click", startSphere);
  $("#back-button").addEventListener("click", backToChoose);
  $("#home-link").addEventListener("click", event => {
    event.preventDefault();
    backToChoose();
  });
  $("#rotate-toggle").addEventListener("click", () => setRotateMode(!rotateMode));
  canvas.addEventListener("pointerdown", pointerDown);
  canvas.addEventListener("pointermove", pointerMove);
  canvas.addEventListener("pointerup", pointerUp);
  canvas.addEventListener("pointercancel", pointerUp);
  window.addEventListener("resize", () => {
    resizeSphere();
    if (!bubbleScreen.hidden) buildBubbleSheet();
  });
})();
