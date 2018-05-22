import React from 'react'
import {parseDiff, getChangeKey, Diff} from 'react-diff-view'

require('react-diff-view/src/Change.css');
require('react-diff-view/src/Diff.css');
require('react-diff-view/src/Hunk.css');
require('react-diff-view/src/Widget.css');

import diffnull0 from 'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diffnull0';
import diff01 from 'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diff01';
import diff12 from 'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diff12';
import diff23 from 'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diff23';
import diff34 from 'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diff34';

let hunks0 = parseDiff(diffnull0)[0].hunks;
let hunks1 = parseDiff(diff01)[0].hunks;
let hunks2 = parseDiff(diff12)[0].hunks;
let hunks3 = parseDiff(diff23)[0].hunks;
let hunks4 = parseDiff(diff34)[0].hunks;

const pages = [
  { hunks: hunks0,
    description: "initial state",
    widgets: [],
  },
  { hunks: hunks1,
    description: "We add an invariant that all account balances must be non-negative",
    widgets: {
      [getChangeKey(hunks1[0].changes[5])]: (<span className="error">sample annotation</span>)
    },
  },
  { hunks: hunks2,
    description: "We need to enforce that transfer amounts are positive",
    widgets: [],
  },
  { hunks: hunks3,
    description: "We add an invariant that `transfer` doesn't create or destroy balance",
    widgets: [],
  },
  { hunks: hunks4,
    description: "We must enforce that the sender and recipient are not the same",
    widgets: [],
  }
];

class AnnotatedCode extends React.Component {
  constructor(props) {
    super(props);
    this.state = { tabIndex: 0 };
  }

  render() {
    let {hunks, description, widgets} = pages[this.state.tabIndex];

    let tabs = (
      <div style={{display: 'flex', flexDirection: 'row'}}>
        {pages.map((_page, index) =>
          <button
            key={index}
            onClick={() => this.setState({tabIndex: index})}
            style={{
              padding: 10,
              margin: 10,
              background: 'transparent',
              border: '2px solid white',
            }}
          >{index}</button>
        )}
      </div>
    );

    return (
      <div>
        <div>
          <h2>select step</h2>
          {tabs}
        </div>
        <div
          style={{
            margin: '20px 0',
          }}
        >{description}</div>
        <Diff hunks={hunks} viewType="unified" widgets={widgets} />
      </div>
    );
  }
}

export default AnnotatedCode
