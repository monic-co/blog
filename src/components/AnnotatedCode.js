import React from 'react'
import {parseDiff, getChangeKey, Diff} from 'react-diff-view'
import styled from "react-emotion"

require('react-diff-view/src/Change.css');
require('react-diff-view/src/Diff.css');
require('react-diff-view/src/Hunk.css');
require('react-diff-view/src/Widget.css');

import diffnull0 from
  'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diffnull0';
import diff01 from
  'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diff01';
import diff12 from
  'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diff12';
import diff23 from
  'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diff23';
import diff34 from
  'raw-loader!../pages/introducing-the-pact-analysis-tools/steps/diff34';

let hunks0 = parseDiff(diffnull0)[0].hunks;
let hunks1 = parseDiff(diff01)[0].hunks;
let hunks2 = parseDiff(diff12)[0].hunks;
let hunks3 = parseDiff(diff23)[0].hunks;
let hunks4 = parseDiff(diff34)[0].hunks;

const Selectors = styled.div`
  display: flex;
  flex-direction: row;
`;

const Wrapper = styled.div`
  margin-top: 40px;
  font-size: 12pt;
`;

const Warning = styled.div`
  background-color: #ffffc6;
  font-family: Consolas, Courier, monospace;
`;

const Button = styled.button`
  padding: 10px;
  margin: 10px;
  background: ${props => props.selected ? 'white' : 'transparent'};
  border: 2px solid white;
`;

const Description = styled.div`
  margin: 20px 0;
`;

const pages = [
  { hunks: hunks0,
    description: <p>The initial contract. We define a schema describing the shape of the data and a table holding rows of that shape. Last, a transfer function which first checks that the sender authorized a transfer and has sufficient funds, then updates both the sending and receiving account balances.</p>,
    widgets: {},
  },
  { hunks: hunks1,
    description: <p>We add an invariant that all account balances must be non-negative. Our toolresponds with example inputs invalidating the invariant. And indeed, we forgot to check for a negative balance, which would allow a user drain (and overdraw) other users' accounts.</p>,
    widgets: {
      [getChangeKey(hunks1[0].changes[14])]: <Warning>(invariant) Invalidating model found: from = "" :: String, to = "" :: String, amount = -39 :: Integer</Warning>,
    },
  },
  { hunks: hunks2,
    description: "The fix is simply to enforce that the amount is positive.",
    widgets: {},
  },
  { hunks: hunks3,
    description: (
      <div>
      <p>
        Now we add a property to check that a transfer doesn't create or destroy money out of thin air. <code>int-column-conserve</code> means "the sum of all balances in the table is preserved".
      </p>
      <p>
        This time the balance looks fine, but it's a bit suspicious that <code>from</code> and <code>to</code> are the same. But looking at the last two lines of the function, we see that, given the example inputs (<code>amount = 1</code>) we end up writing the new balance as <code>from-bal - 1</code> and the <em>overwriting</em> it with <code>to-bal + 1</code>, effectively creating $1 out of thin air.
      </p>
      </div>
    ),
    widgets: {
      [getChangeKey(hunks3[0].changes[17])]: <Warning>Invalidating model found: from = "" :: String, to = "" :: String, amount = 1 :: Integer</Warning>,
    },
  },
  { hunks: hunks4,
    description: <p>We choose the easiest fix -- enforcing that the sender and recipient are not the same account.</p>,
    widgets: {},
  }
];

export default class AnnotatedCode extends React.Component {
  constructor(props) {
    super(props);
    this.state = { tabIndex: 0 };
  }

  componentDidMount() {
    document.onkeydown = e => {
      switch (e.keyCode) {
        case 37: // left arrow
          this.setState(({tabIndex}) =>
            ({tabIndex: Math.max(tabIndex - 1, 0)})
          );
          break;
        case 39: // right arrow
          this.setState(({tabIndex}) =>
            ({tabIndex: Math.min(tabIndex + 1, pages.length - 1)})
          );
          break;
      }
    };
  }

  render() {
    let {tabIndex} = this.state;
    let {hunks, description, widgets} = pages[tabIndex];

    let tabs = (
      <Selectors>
        {pages.map((_page, index) =>
          <Button
            key={index}
            selected={index == tabIndex}
            onClick={() => this.setState({tabIndex: index})}
          >{index}</Button>
        )}
      </Selectors>
    );

    return (
      <Wrapper>
        <div>{tabs}</div>
        <Description>{description}</Description>
        <Diff hunks={hunks} viewType="unified" widgets={widgets} />
      </Wrapper>
    );
  }
}
